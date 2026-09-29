"use strict";

/* ================= TOTP core (RFC 6238) ================= */
const B32='ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
function base32Decode(input){
  const s=input.replace(/=+$/,'').replace(/\s+/g,'').toUpperCase();
  if(!s) throw new Error('Kunci kosong');
  let bits=0,val=0;const out=[];
  for(const ch of s){
    const idx=B32.indexOf(ch);
    if(idx===-1) throw new Error('Karakter Base32 tidak valid: "'+ch+'"');
    val=(val<<5)|idx;bits+=5;
    if(bits>=8){out.push((val>>>(bits-8))&0xff);bits-=8;}
  }
  return new Uint8Array(out);
}
const HASH={SHA1:'SHA-1',SHA256:'SHA-256',SHA512:'SHA-512'};
async function totp(acc,when){
  const t=(when??Date.now())/1000, period=acc.period||30;
  const counter=Math.floor(t/period);
  const buf=new ArrayBuffer(8), dv=new DataView(buf);
  dv.setUint32(0, Math.floor(counter/2**32), false);
  dv.setUint32(4, counter>>>0, false);
  const key=base32Decode(acc.secret);
  const ck=await crypto.subtle.importKey('raw',key,{name:'HMAC',hash:{name:HASH[acc.algorithm||'SHA1']||'SHA-1'}},false,['sign']);
  const mac=new Uint8Array(await crypto.subtle.sign('HMAC',ck,buf));
  const off=mac[mac.length-1]&0x0f;
  const bin=((mac[off]&0x7f)<<24)|(mac[off+1]<<16)|(mac[off+2]<<8)|mac[off+3];
  const d=acc.digits||6;
  return (bin%(10**d)).toString().padStart(d,'0');
}
function parseOtpauth(uri){
  const u=new URL(uri.trim());
  if(u.protocol!=='otpauth:') throw new Error('Bukan tautan otpauth');
  if(u.host.toLowerCase()!=='totp') throw new Error('Hanya TOTP yang didukung');
  const p=u.searchParams, secret=p.get('secret');
  if(!secret) throw new Error('Tautan tidak punya secret');
  let issuer=p.get('issuer')||'', account=decodeURIComponent(u.pathname.replace(/^\//,''));
  if(account.includes(':')){const[a,b]=account.split(':');if(!issuer)issuer=a;account=b.trim();}
  return {secret:secret.replace(/\s/g,''),issuer,account,
    digits:parseInt(p.get('digits'))||6,period:parseInt(p.get('period'))||30,
    algorithm:(p.get('algorithm')||'SHA1').toUpperCase()};
}

/* ================= encryption (PBKDF2 + AES-GCM) ================= */
const VKEY='kunci.vault.v2', PREF='kunci.pref.v2', ITER=310000;
function b64(bytes){let s='';bytes.forEach(b=>s+=String.fromCharCode(b));return btoa(s);}
function ub64(str){const bin=atob(str),a=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)a[i]=bin.charCodeAt(i);return a;}
async function deriveKey(password,salt,iter){
  const base=await crypto.subtle.importKey('raw',new TextEncoder().encode(password),'PBKDF2',false,['deriveKey']);
  return crypto.subtle.deriveKey({name:'PBKDF2',salt,iterations:iter,hash:'SHA-256'},base,
    {name:'AES-GCM',length:256},false,['encrypt','decrypt']);
}
async function encrypt(key,obj){
  const iv=crypto.getRandomValues(new Uint8Array(12));
  const ct=await crypto.subtle.encrypt({name:'AES-GCM',iv},key,new TextEncoder().encode(JSON.stringify(obj)));
  return {iv:b64(iv),ct:b64(new Uint8Array(ct))};
}
async function decrypt(key,iv_b64,ct_b64){
  const pt=await crypto.subtle.decrypt({name:'AES-GCM',iv:ub64(iv_b64)},key,ub64(ct_b64));
  return JSON.parse(new TextDecoder().decode(pt));
}
function readVault(){try{return JSON.parse(localStorage.getItem(VKEY)||'null');}catch(e){return null;}}
async function writeVault(key,accounts){
  const enc=await encrypt(key,accounts);
  const v=readVault();
  localStorage.setItem(VKEY,JSON.stringify({ver:2,salt:v.salt,iter:v.iter,iv:enc.iv,ct:enc.ct}));
}
function getPref(){try{return JSON.parse(localStorage.getItem(PREF)||'{}');}catch(e){return {};}}
function setPref(p){try{localStorage.setItem(PREF,JSON.stringify(p));}catch(e){}}

/* ================= state ================= */
let masterKey=null, accounts=[], rafId=null, autolockMs=60000, idleTimer=null;

/* ================= DOM ================= */
const $=id=>document.getElementById(id);
const lockScreen=$('lockScreen'),app=$('app'),fab=$('addBtn'),listEl=$('list');
const R=20,C=2*Math.PI*R;

/* ---- lock / setup flow ---- */
function showLock(mode){ // mode: 'unlock' | 'create'
  stopTick(); stopScan(); masterKey=null; accounts=[];
  app.classList.add('hidden'); fab.classList.add('hidden');
  closeAll();
  lockScreen.classList.remove('hidden');
  const pw2=$('pw2');
  if(mode==='create'){
    $('lockTitle').textContent='Buat brankas';
    $('lockDesc').textContent='Pilih kata sandi utama. Dipakai untuk mengenkripsi semua kode di perangkat ini.';
    $('lockGo').textContent='Buat brankas';
    pw2.classList.remove('hidden');
    $('lockNote').textContent='Kata sandi ini tidak bisa dipulihkan. Kalau lupa, kamu harus reset dan menambah ulang akun.';
  }else{
    $('lockTitle').textContent='Buka Kunci';
    $('lockDesc').textContent='Masukkan kata sandi utama untuk membuka brankasmu.';
    $('lockGo').textContent='Buka';
    pw2.classList.add('hidden');
    $('lockNote').textContent='';
  }
  lockScreen.dataset.mode=mode;
  $('pw1').value='';pw2.value='';$('lockErr').textContent='';
  setTimeout(()=>$('pw1').focus(),100);
}

async function handleLockGo(){
  const mode=lockScreen.dataset.mode, pw=$('pw1').value;
  const err=$('lockErr');
  if(!pw){err.textContent='Masukkan kata sandi.';return;}
  $('lockGo').disabled=true;
  try{
    if(mode==='create'){
      if(pw.length<6){err.textContent='Minimal 6 karakter.';return;}
      if(pw!==$('pw2').value){err.textContent='Kata sandi tidak sama.';return;}
      const salt=crypto.getRandomValues(new Uint8Array(16));
      const key=await deriveKey(pw,salt,ITER);
      const enc=await encrypt(key,[]);
      localStorage.setItem(VKEY,JSON.stringify({ver:2,salt:b64(salt),iter:ITER,iv:enc.iv,ct:enc.ct}));
      masterKey=key; accounts=[];
      enterApp();
    }else{
      const v=readVault();
      const key=await deriveKey(pw,ub64(v.salt),v.iter||ITER);
      accounts=await decrypt(key,v.iv,v.ct); // throws on wrong password
      masterKey=key;
      enterApp();
    }
  }catch(e){
    err.textContent = (mode==='unlock') ? 'Kata sandi salah.' : ('Gagal: '+e.message);
  }finally{ $('lockGo').disabled=false; }
}
$('lockGo').addEventListener('click',handleLockGo);
$('pw1').addEventListener('keydown',e=>{if(e.key==='Enter'){if(lockScreen.dataset.mode==='create')$('pw2').focus();else handleLockGo();}});
$('pw2').addEventListener('keydown',e=>{if(e.key==='Enter')handleLockGo();});

function enterApp(){
  lockScreen.classList.add('hidden');
  app.classList.remove('hidden'); fab.classList.remove('hidden');
  autolockMs = getPref().autolock ?? 60000;
  $('autolockSel').value=String(autolockMs);
  build(); startTick(); resetIdle();
}

async function persist(){ if(masterKey) await writeVault(masterKey,accounts); }

/* ================= render ================= */
function esc(s){return String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));}
function fmt(code){const mid=Math.ceil(code.length/2);
  return esc(code.slice(0,mid))+'<span style="width:.28em;display:inline-block"></span>'+esc(code.slice(mid));}

function build(){
  const q=($('searchIn').value||'').toLowerCase().trim();
  const items=accounts.map((a,i)=>({a,i}))
    .filter(({a})=>!q||((a.issuer||'')+' '+(a.account||'')).toLowerCase().includes(q));
  if(accounts.length===0){
    listEl.innerHTML=`<div class="empty"><strong>Brankas kosong</strong><span>Ketuk “Tambah akun” untuk scan QR code atau memasukkan kunci secara manual.</span></div>`;return;
  }
  if(items.length===0){listEl.innerHTML=`<div class="empty"><span>Tidak ada yang cocok dengan pencarianmu.</span></div>`;return;}
  listEl.innerHTML=items.map(({a,i})=>`
    <div class="card" data-i="${i}">
      <div class="meta">
        <div class="issuer">${esc(a.issuer||'Akun')}</div>
        <div class="label">${esc(a.account||'')}</div>
        <div class="code" data-code="${i}" title="Ketuk untuk menyalin">••• •••</div>
      </div>
      <div class="ring"><svg width="46" height="46">
        <circle cx="23" cy="23" r="${R}" fill="none" stroke="var(--ring-track)" stroke-width="3.5"/>
        <circle class="prog" data-prog="${i}" cx="23" cy="23" r="${R}" fill="none" stroke="var(--gold)" stroke-width="3.5"
          stroke-linecap="round" stroke-dasharray="${C.toFixed(1)}" stroke-dashoffset="0"/>
      </svg><div class="rem" data-rem="${i}">30</div></div>
      <div class="copied" data-copied="${i}">Disalin</div>
      <button class="del" data-del="${i}" title="Hapus">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><polyline points="3 6 5 6 21 6"/><path d="M19 6l-1 14a2 2 0 0 1-2 2H8a2 2 0 0 1-2-2L5 6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/></svg>
      </button>
    </div>`).join('');
}

async function tick(){
  const now=Date.now();
  for(let i=0;i<accounts.length;i++){
    const a=accounts[i],period=(a.period||30)*1000, rem=period-(now%period), remS=Math.ceil(rem/1000);
    const prog=listEl.querySelector(`[data-prog="${i}"]`), remEl=listEl.querySelector(`[data-rem="${i}"]`);
    if(prog){prog.style.strokeDashoffset=(C*(1-rem/period)).toFixed(1);prog.style.stroke=remS<=5?'var(--danger)':'var(--gold)';}
    if(remEl){remEl.textContent=remS;remEl.style.color=remS<=5?'var(--danger)':'var(--ink-dim)';}
    const codeEl=listEl.querySelector(`[data-code="${i}"]`);
    if(codeEl){try{const c=await totp(a,now);if(codeEl.dataset.val!==c){codeEl.dataset.val=c;codeEl.innerHTML=fmt(c);}}
      catch(e){codeEl.textContent='error';codeEl.style.color='var(--danger)';}}
  }
  rafId=requestAnimationFrame(()=>setTimeout(tick,250));
}
function startTick(){stopTick();tick();}
function stopTick(){if(rafId)cancelAnimationFrame(rafId);rafId=null;}

/* card interactions */
listEl.addEventListener('click',e=>{
  const codeEl=e.target.closest('[data-code]');
  if(codeEl){const v=codeEl.dataset.val;if(!v)return;navigator.clipboard?.writeText(v).catch(()=>{});
    const tag=listEl.querySelector(`[data-copied="${codeEl.dataset.code}"]`);
    if(tag){tag.classList.add('show');setTimeout(()=>tag.classList.remove('show'),1100);}return;}
  const del=e.target.closest('[data-del]');
  if(del){const i=+del.dataset.del;
    if(confirm(`Hapus ${accounts[i].issuer||'akun'} — ${accounts[i].account||''}?`)){
      accounts.splice(i,1);persist();build();}}
});
$('searchIn').addEventListener('input',build);

/* ================= add sheet ================= */
const scrim=$('scrim');
function openSheet(el){scrim.classList.add('open');el.classList.add('open');}
function closeAll(){scrim.classList.remove('open');
  document.querySelectorAll('.sheet').forEach(s=>s.classList.remove('open'));stopScan();}
scrim.addEventListener('click',closeAll);

$('addBtn').addEventListener('click',()=>{openSheet($('addSheet'));switchTab('scan');});
$('addCancel').addEventListener('click',closeAll);
$('scanCancel').addEventListener('click',closeAll);

function switchTab(which){
  const scan=which==='scan';
  $('tabScan').classList.toggle('on',scan);$('tabManual').classList.toggle('on',!scan);
  $('scanPane').classList.toggle('hidden',!scan);$('manualPane').classList.toggle('hidden',scan);
  if(scan) startScan(); else stopScan();
}
$('tabScan').addEventListener('click',()=>switchTab('scan'));
$('tabManual').addEventListener('click',()=>switchTab('manual'));

/* ---- QR scanner ---- */
let stream=null, scanLoop=null, canvas=document.createElement('canvas'), ctx=canvas.getContext('2d',{willReadFrequently:true});
async function startScan(){
  const status=$('scanStatus'), video=$('video');
  if(stream)return;
  try{
    stream=await navigator.mediaDevices.getUserMedia({video:{facingMode:'environment'}});
    video.srcObject=stream; await video.play();
    status.textContent='Arahkan kamera ke QR code…';
    const detector=('BarcodeDetector'in window)?new window.BarcodeDetector({formats:['qr_code']}):null;
    scanLoop=setInterval(async()=>{
      if(video.readyState<2)return;
      let text=null;
      try{
        if(detector){const codes=await detector.detect(video);if(codes.length)text=codes[0].rawValue;}
        else if(window.jsQR){
          canvas.width=video.videoWidth;canvas.height=video.videoHeight;
          ctx.drawImage(video,0,0,canvas.width,canvas.height);
          const img=ctx.getImageData(0,0,canvas.width,canvas.height);
          const r=window.jsQR(img.data,img.width,img.height);if(r)text=r.data;
        }else{status.textContent='Browser ini tak bisa scan — pakai tab Manual.';}
      }catch(e){}
      if(text) onScanResult(text);
    },350);
  }catch(e){
    status.textContent='Kamera tak bisa diakses. Pakai tab Manual.';
  }
}
function stopScan(){
  if(scanLoop){clearInterval(scanLoop);scanLoop=null;}
  if(stream){stream.getTracks().forEach(t=>t.stop());stream=null;}
  const v=$('video'); if(v) v.srcObject=null;
}
async function onScanResult(text){
  if(!text.toLowerCase().startsWith('otpauth://')){$('scanStatus').textContent='QR bukan kode otpauth. Coba lagi.';return;}
  stopScan();
  try{
    const acc=parseOtpauth(text); await totp(acc);
    accounts.push(acc); await persist(); build();
    closeAll();
  }catch(e){$('scanStatus').textContent='Gagal membaca: '+e.message; startScan();}
}

/* ---- manual add ---- */
$('secret').addEventListener('input',()=>{
  const v=$('secret').value.trim();
  if(v.toLowerCase().startsWith('otpauth://')){
    try{const p=parseOtpauth(v);$('secret').value=p.secret;
      if(p.issuer)$('issuer').value=p.issuer;if(p.account)$('account').value=p.account;
      $('secret').dataset.opts=JSON.stringify({digits:p.digits,period:p.period,algorithm:p.algorithm});
      $('addErr').textContent='';
    }catch(e){$('addErr').textContent=e.message;}
  }else delete $('secret').dataset.opts;
});
$('saveBtn').addEventListener('click',async()=>{
  const err=$('addErr');err.textContent='';
  const raw=$('secret').value.trim();
  if(!raw){err.textContent='Masukkan kunci rahasia dulu.';return;}
  let acc;
  try{
    if(raw.toLowerCase().startsWith('otpauth://'))acc=parseOtpauth(raw);
    else{const o=$('secret').dataset.opts?JSON.parse($('secret').dataset.opts):{};
      acc={secret:raw.replace(/\s/g,''),issuer:$('issuer').value.trim(),account:$('account').value.trim(),
        digits:o.digits||6,period:o.period||30,algorithm:o.algorithm||'SHA1'};}
    if(!acc.issuer)acc.issuer=$('issuer').value.trim();
    if(!acc.account)acc.account=$('account').value.trim();
    $('saveBtn').disabled=true;
    await totp(acc);
    accounts.push(acc);await persist();build();
    $('secret').value=$('issuer').value=$('account').value='';delete $('secret').dataset.opts;
    closeAll();
  }catch(e){err.textContent=e.message||'Kunci tidak valid.';}
  finally{$('saveBtn').disabled=false;}
});

/* ================= settings ================= */
$('settingsBtn').addEventListener('click',()=>{openSheet($('setSheet'));$('setMsg').textContent='';$('importArea').classList.add('hidden');});
$('setClose').addEventListener('click',closeAll);
$('lockBtn').addEventListener('click',()=>showLock('unlock'));

$('autolockSel').addEventListener('change',e=>{
  autolockMs=+e.target.value; const p=getPref();p.autolock=autolockMs;setPref(p);resetIdle();
});

$('exportBtn').addEventListener('click',async()=>{
  const blob=localStorage.getItem(VKEY);
  try{await navigator.clipboard.writeText(blob);$('setMsg').textContent='Backup terenkripsi disalin ke clipboard.';}
  catch(e){
    // fallback: show in the import textarea for manual copy
    $('importArea').classList.remove('hidden');$('importText').value=blob;$('importText').select();
    $('setMsg').textContent='Salin teks di kotak bawah.';
  }
});
$('importToggle').addEventListener('click',()=>$('importArea').classList.toggle('hidden'));
$('importBtn').addEventListener('click',async()=>{
  const err=$('importErr');err.textContent='';
  const txt=$('importText').value.trim();
  if(!txt){err.textContent='Tempel teks backup dulu.';return;}
  try{
    const v=JSON.parse(txt);
    if(!v.salt||!v.iv||!v.ct)throw new Error('Format backup tidak dikenali.');
    localStorage.setItem(VKEY,JSON.stringify(v));
    $('setMsg').textContent='Brankas dipulihkan. Membuka ulang…';
    setTimeout(()=>showLock('unlock'),700);
  }catch(e){err.textContent='Gagal: '+e.message;}
});

$('changePwBtn').addEventListener('click',async()=>{
  const err=$('pwErr');err.textContent='';
  const cur=$('curPw').value, np=$('newPw').value, np2=$('newPw2').value;
  if(np.length<6){err.textContent='Kata sandi baru minimal 6 karakter.';return;}
  if(np!==np2){err.textContent='Kata sandi baru tidak sama.';return;}
  try{
    const v=readVault();
    await deriveKey(cur,ub64(v.salt),v.iter||ITER).then(k=>decrypt(k,v.iv,v.ct)); // verify old pw
    const salt=crypto.getRandomValues(new Uint8Array(16));
    const key=await deriveKey(np,salt,ITER);
    const enc=await encrypt(key,accounts);
    localStorage.setItem(VKEY,JSON.stringify({ver:2,salt:b64(salt),iter:ITER,iv:enc.iv,ct:enc.ct}));
    masterKey=key;
    $('curPw').value=$('newPw').value=$('newPw2').value='';
    $('setMsg').textContent='Kata sandi diperbarui.';
  }catch(e){err.textContent='Kata sandi lama salah.';}
});

$('wipeBtn').addEventListener('click',()=>{
  if(confirm('Ini menghapus SEMUA akun dan brankas dari perangkat ini. Yakin?')){
    localStorage.removeItem(VKEY);showLock('create');
  }
});

/* ================= auto-lock ================= */
function resetIdle(){
  clearTimeout(idleTimer);
  if(autolockMs>0 && masterKey) idleTimer=setTimeout(()=>showLock('unlock'), autolockMs);
}
['click','keydown','touchstart','mousemove'].forEach(ev=>
  document.addEventListener(ev,()=>{if(masterKey)resetIdle();},{passive:true}));
document.addEventListener('visibilitychange',()=>{
  if(document.hidden){stopScan();}
});

/* ================= boot ================= */
(function boot(){
  if(!('crypto'in window)||!crypto.subtle){
    document.body.innerHTML='<div class="lock"><h2>Tidak didukung</h2><p>Butuh HTTPS &amp; browser modern untuk enkripsi.</p></div>';return;
  }
  showLock(readVault()?'unlock':'create');
})();

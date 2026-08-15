(function(){
  if (location.hash) {
    try {
      var tgt = document.querySelector(location.hash);
      if (tgt) tgt.scrollIntoView({behavior:'instant', block:'start'});
    } catch(e){}
  }

  var hdr = document.getElementById('hdr');
  if (hdr) {
    var onScroll = function(){ hdr.classList.toggle('stuck', window.scrollY > 8); };
    onScroll(); window.addEventListener('scroll', onScroll, {passive:true});
  }

  // tabs
  var tabs = Array.prototype.slice.call(document.querySelectorAll('.tab'));
  tabs.forEach(function(t){
    t.addEventListener('click', function(){
      tabs.forEach(function(o){
        o.setAttribute('aria-selected', String(o === t));
        document.getElementById(o.getAttribute('aria-controls')).hidden = (o !== t);
      });
    });
    t.addEventListener('keydown', function(e){
      var i = tabs.indexOf(t), n = null;
      if (e.key === 'ArrowRight') n = tabs[(i+1)%tabs.length];
      if (e.key === 'ArrowLeft')  n = tabs[(i-1+tabs.length)%tabs.length];
      if (n){ e.preventDefault(); n.click(); n.focus(); }
    });
  });

  // copy buttons on terminal blocks
  document.querySelectorAll('.term').forEach(function(block){
    var btn = document.createElement('button');
    btn.className = 'copy'; btn.type = 'button'; btn.textContent = 'copy';
    btn.addEventListener('click', function(){
      var clone = block.cloneNode(true);
      var cb = clone.querySelector('.copy');
      if (cb) cb.remove();
      var text = clone.innerText.replace(/^\s*\$\s?/gm, '')
        .split('\n').filter(function(l){ return !/^OK — /.test(l) && !/^\s{4,}/.test(l); }).join('\n').trim();
      var done = function(){
        btn.textContent = 'copied'; btn.classList.add('done');
        setTimeout(function(){ btn.textContent = 'copy'; btn.classList.remove('done'); }, 1600);
      };
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(done, function(){ fallback(text, done); });
      } else { fallback(text, done); }
    });
    block.appendChild(btn);
  });
  function fallback(text, done){
    var ta = document.createElement('textarea');
    ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
    document.body.appendChild(ta); ta.select();
    try { document.execCommand('copy'); done(); } catch(e){}
    document.body.removeChild(ta);
  }
})();

(function(){
  var hdr = document.getElementById('hdr');
  if (hdr) {
    var onScroll = function(){ hdr.classList.toggle('stuck', window.scrollY > 8); };
    onScroll(); window.addEventListener('scroll', onScroll, {passive:true});
  }

  // Close the small-screen menu after a choice.
  document.querySelectorAll('details.menu a').forEach(function(a){
    a.addEventListener('click', function(){ var d = a.closest('details'); if (d) d.removeAttribute('open'); });
  });

  // Copy buttons on command blocks: copy the commands only, never the printed verdicts.
  document.querySelectorAll('.term[data-copy]').forEach(function(block){
    var btn = document.createElement('button');
    btn.className = 'copy'; btn.type = 'button'; btn.textContent = 'copy';
    btn.addEventListener('click', function(){
      var text = Array.prototype.map.call(block.querySelectorAll('.cmd'), function(n){ return n.textContent; }).join('\n');
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

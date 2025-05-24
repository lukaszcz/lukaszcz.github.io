document.addEventListener("DOMContentLoaded", function(){
  const toc = document.querySelector('.sidebar__right .toc');
  if (toc) {
    Object.assign(toc.style, {
      position: 'sticky',
      top: '2rem',
      maxHeight: 'calc(100vh - 4rem)',
      overflowY: 'auto'
    });
  }
});

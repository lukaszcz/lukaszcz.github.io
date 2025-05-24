document.addEventListener("DOMContentLoaded", function(){
  const aside = document.querySelector(".sidebar__right");
  if (!aside) return;

  Object.assign(aside.style, {
    position: "sticky",
    top: "2rem",
    maxHeight: "calc(100vh - 4rem)",
    overflowY: "auto",
    zIndex: "1"
  });
});

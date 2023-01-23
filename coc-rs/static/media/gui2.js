
const canvas = document.getElementById("background_canvas")
const context = canvas.getContext("2d")

function center (element){
  const bounds =element.getBoundingClientRect();
  return [bounds.left+ bounds.width / 2,bounds.top +bounds.height / 2]
}

function redraw_lines() {
  scale = window.devicePixelRatio;
  canvas.width = Math.floor (window.innerWidth * scale);
  canvas.height = Math.floor (window.innerHeight * scale);
  context.scale(scale, scale);
  for (const element of document.querySelectorAll(".metavariable_name_id")){
    const target = document.getElementById(`metavariable_${element.dataset.targetid}`);
    context.strokeStyle = target.dataset.color;
    context.lineWidth = 2;
    context.beginPath();
    context.moveTo(...center(element));
    context.lineTo(...center(target));
    context.stroke();
  }
}

let animate_until = Date.now();
function frame() {
  if (Date.now() < animate_until) {
    redraw_lines();
  }
  window.requestAnimationFrame(frame);
}
frame()

function update_display() {
  animate_until = Date.now() + 500;
}

window.addEventListener ("resize",redraw_lines);

start_qadwg({
  app_element: document.getElementById("app"),
  on_replace_dom: update_display,
});
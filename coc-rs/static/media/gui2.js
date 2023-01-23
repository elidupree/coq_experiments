
const canvas = document.getElementById("background_canvas")
const context = canvas.getContext("2d")

const last_bounds_by_id = {};

function center (element){
  const bounds =element.getBoundingClientRect();
  return [bounds.left+ bounds.width / 2,bounds.top +bounds.height / 2]
}

function redraw_lines() {
  scale = window.devicePixelRatio;
  const bounds = document.body.getBoundingClientRect();
  canvas.style.width = bounds.width+"px";
  canvas.style.height = bounds.height+"px";
  canvas.width = Math.floor (bounds.width * scale);
  canvas.height = Math.floor (bounds.height * scale);
  context.scale(scale, scale);
  for (const element of document.querySelectorAll(".metavariable_reference")){
    const target = document.getElementById(`metavariable_${element.dataset.targetid}`);
    context.strokeStyle = target.dataset.color;
    context.lineWidth = 2;
    context.beginPath();
    context.moveTo(...center(element));
    context.lineTo(...center(target));
    context.stroke();
  }
}

const transition_seconds = 0.2;
let moving_elements = [];
let just_changed = false;
let animate_until = Date.now();
function frame() {
  if (just_changed) {
    for (const element of document.querySelectorAll(".node")) {
      const bounds = element.getBoundingClientRect();
      const last_bounds = last_bounds_by_id[element.id];
      if (last_bounds !== undefined) {
        if (bounds.x !== last_bounds.x || bounds.y !== last_bounds.y) {
          const dx = last_bounds.x - bounds.x;
          const dy = last_bounds.y - bounds.y;
          element.style.transition = "";
          element.style.transform = `translate(${dx}px, ${dy}px)`;
          console.log("uh", element.style.transform)
          moving_elements.push(element);
        }
      }
      last_bounds_by_id[element.id] = bounds;
    }
  }
  if (Date.now() < animate_until) {
    redraw_lines();
    if (!just_changed) {
      for (const element of moving_elements) {
        element.style.transition = `all ${transition_seconds}s ease-out`;
        element.style.transform = "translate(0px, 0px)";
      }
      moving_elements = [];
    }
  }
  just_changed = false;
  window.requestAnimationFrame(frame);
}
frame()

function update_display() {
  just_changed = true;
  animate_until = Date.now() + (transition_seconds + 0.1)*1000;
}

window.addEventListener ("resize",update_display);

start_qadwg({
  app_element: document.getElementById("app"),
  on_replace_dom: update_display,
});
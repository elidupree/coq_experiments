
const main_interface_element = document.getElementById ("main_interface")

let socket = null
let interface_ready = false
let app_options = {}

function send_to_socket(variant, contents) {
  if (socket !== null && socket.readyState == 1) {
    socket.send(JSON.stringify({[variant]: contents}))
  }
}

function connect() {
    if (socket) { socket.close() }
    socket = new WebSocket(`ws://${location.host}/qadwg_session`)

    socket.onopen = () => {
      console.log('Connected')
    }

    socket.onmessage = (ev) => {
      //console.log('Received: ' + ev.data)
      const message = JSON.parse(ev.data)
      // console.log('Received: ', message)
      if (message["ReplaceDom"]) {
        console.log('Replacing DOM');
        if (app_options.app_element === undefined) {
          app_options.app_element = document.createElement("div");
          document.body.appendChild(app_options.app_element)
        }
        morphdom(app_options.app_element, message["ReplaceDom"]);
        if (app_options.on_replace_dom) {
          app_options.on_replace_dom()
        }
      }
      else if (message["AppMessage"]) {
        console.log('Got app message');
        if (app_options["message_handler"]) {
          app_options["message_handler"](JSON.parse(message["AppMessage"]));
        }
      }
    }

    socket.onclose = () => {
      console.log('Disconnected')
      setTimeout(() => connect(), 1000)
    }

}

function start_qadwg(options) {
  app_options = options
  connect()
}
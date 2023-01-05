use typed_html::elements::FlowContent;
use typed_html::{html, text};

pub type Element = Box<dyn FlowContent<String>>;

fn global(g: &GlobalTerm) -> Element {
    html! {
        <div class="global">
            <div class="name">
                {text!("{}", g.name)}
            </div>
            <div class="value">
                {text!("{}", g.value.display())}
            </div>
            <div class="type">
                {text!("{}", g.ty.display())}
            </div>
            <button onclick={callback(move || put_in_current_goal(g))}>
                Use
            </button>
        </div>
    }
}

fn context_element(context: Context) -> Element {
    let entries = context.entries().map(|entry| {
        html! {
            <div class="entry" onclick={callback(move || focus(id))}>
                <div class="name">
                    {text!("{}", entry.name)}
                </div>
                <div class="type">
                    {text!("{}", entry.ty.display())}
                </div>
                <button onclick={callback(move || put_in_current_goal(entry))}>
                    Use
                </button>
            </div>
        }
    });
    html! {
        <div class="context">
            {entries}
        </div>
    }
}

fn focus(id: TermId) {}

fn node_parents(term: &Node) -> Option<Element> {
    let active_parent = term.active_parent()?;
    let parents = term.parents().map(|parent| {
        html! {
            <div class="parent" onclick={callback(move || focus(id))}>
                <div class="name">
                    {text!("{}", parent.name)}
                </div>
            </div>
        }
    });
    Some(html! {
        <div class="parents">
            <div class="active">
                {node_element(active_parent, false, 0)}
            </div>
            <div class="other">
                {parents}
            </div>
        </div>
    })
}

fn node_children(term: &Node, depth: usize) -> Element {
    let children = term.children().map(|child| {
        node_element(child, depth);
    });
    html! {
        <div class="children">
            {children}
        </div>
    }
}

fn node_element(term: &Node, focused: bool, depth: usize) -> Element {
    let id = term.id;
    let mut elements: Vec<Element> = Vec::new();
    if focused {
        elements.push(context_element(term));
    }
    elements.push(html! {
        <div class="name">
            {text!("{}", g.name)}
        </div>
    });
    elements.push(html! {
        <div class="value">
            {text!("{}", g.value.display())}
        </div>
    });
    elements.push(html! {
        <div class="type">
            {text!("{}", g.ty.display())}
        </div>
    });
    if something {
        elements.push(html! {
            <button onclick={callback(move || insert_lambda(id))}>
                Lambda
            </button>
        });
        elements.push(html! {
            <button onclick={callback(move || insert_forall(id))}>
                ForAll
            </button>
        });
        elements.push(html! {
            <button onclick={callback(move || insert_apply(id))}>
                Apply
            </button>
        });
    }
    if something {
        elements.push(html! {
            <button onclick={callback(move || clear(id))}>
                Clear
            </button>
        });
    }
    html! {
        <div class="node" onclick={callback(move || focus(id))}>
            {(focused).then(|| node_parents(term))}
            <div class="self" onclick={callback(move || focus(id))}>
                {elements}
            </div>
            {(depth > 0).then(|| node_children(term, depth - 1))}
        </div>
    }
}

fn new_global(name: String) {}

fn globals() -> Element {
    let individual_globals = context.globals.iter().map(|g| global(g));
    html! {
        <div class="globals">
            {individual_globals}
            <div class="new_global">
                <input id="new_global_name" type="text"/>
                <button onclick={callback_with(r##"$("#new_global_name").value"##, new_global)}>
                    Create
                </button>
            </div>
        </div>
    }
}

fn whole_page() -> Element {
    let globals = globals();
    let goals = goals().map(|term| node_element(term, false, 0));
    html! {
        <div class="page">
            <div class="globals">
                {globals}
            </div>
            {node_element(active_node(), true, 2)}
            <div class="goals">
                {goals}
            </div>
        </div>
    }
}

#[actix_web::main]
async fn main() {
    quick_and_dirty_web_gui::launch(4986).await;
}

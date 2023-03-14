#h = "hole"
i = "implies" # "→"
d = "delay" # "►"
u = "unfoldsto" # "↬"
v = "var" # "𝒱"
#l = "lambda"

axioms = [
    ["A", ((i, "A"), "B"), "B"],
    ["B", ((i,"A"), "B")],
    [
        ((i,"A"),"B"),
        ((i, ((i,"C"),"A")), ((i,"C"),"B"))
    ],
    ["A", (d, "A")],
    [(d, "A"), "A"],
    [
        ((i,"A"),"B"),
        ((i, (d, "A")), (d, "B"))
    ],
    [((u,((("λ","★"),"B"),"v")), "v")],
    [((u,((("λ","○"),"B"),"v")), "B")],
    [((u,((("λ","a"),"B"),"c")),"d"),
     ((u,((("λ","e"),"F"),"g")),"h"),
     ((u,((("λ", ("a","e")),("B","F")),("c","g"))), ("d","h"))],
    [
        (("λ","x"),"B"),
        ((u,((("λ","x"),"B"),"v")), "C"),
        (d, "C")
    ],
    [
        (((u,(("λ","x"),"B")),(v, "B")), "C"),
        "C",
        (("λ","x"),"B")
    ],
]

def render_axiom (axiom):
    variables = set()
    def render_proposition(proposition):
        if type(proposition) is tuple:
            a,b = tuple(render_proposition(a) for a in proposition)
            return f"a({a}, {b})"
        if proposition [0].isupper():
            variables.add (proposition)
            return proposition
        return f"'{proposition}'"

    props = [render_proposition(p) for p in axiom]
    premises = ", ".join (props[:-1])
    conclusion = props[-1]
    if len(props) > 1:
        meta_axiom = f"{conclusion} :- {premises}."
    else:
        meta_axiom = conclusion+"."

    embedded_form = axiom [- 1]
    for premise in reversed (axiom [:-1]):
        embedded_form = ((i, premise), embedded_form)

    def variable_locations(proposition, variable):
        if type(proposition) is tuple:
            a,b = tuple(variable_locations(a, variable) for a in proposition)
            if a == ("○","○"):
                a = "○"
            if b == ("○","○"):
                b = "○"
            return (a,b)
        if proposition [0] == variable:
            return "★"
        else:
            return "○"

    for variable in sorted (variables):
        embedded_form = (("λ", variable_locations(embedded_form, variable)), embedded_form)

    def render_embedded(proposition):
        if type(proposition) is tuple:
            a,b = tuple(render_proposition(a) for a in proposition)
            return f"a({a}, {b})"
        if proposition [0].isupper():
            return "'○'"
        return f"'{proposition}'"

    embedded_axiom = render_embedded(embedded_form)+"."

    return meta_axiom, embedded_axiom


#
# def normal_axiom(axiom):
#     premises = ", ".join (axiom[:-1])
#     return f"{axiom[-1]} :- {premises}"
#
# def embedded_axiom(axiom):
#     variables =
#     premises = ", ".join (axiom[:-1])
#     return f"{axiom[-1]} :- {premises}"

for axiom in axioms:
    m,e = render_axiom(axiom)
    print(m)
    print(e)
solvers = "assumption reflexivity contradiction constructor discriminate injection".split() + ["decide equality"] + "trivial tauto dtauto congruence firstorder easy auto eauto".split() + ["auto with *", "eauto with *"]
progress = "subst".split()

print(f'''
  assert_succeeds (first [
    {"".join(f'report_solved ({a}) "`{a}` solves it" | ' for a in solvers)}
    {"".join(f'report_progress ({a}) "`{a}` makes progress" | ' for a in progress)}
    idtac
  ]).
''')
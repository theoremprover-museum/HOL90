val window_lib = new_library{
    name    = "window",
    doc     = "Support for transformational reasoning, by Jim Grundy",
    path    = "/users/jug/bigdisc/hol90/library/window/",
    parents = [hol_lib],
    theories= ["window"],
    code    = ["ml_ext.sml", "hol_ext.sml", "relations.sml", "rules.sml",
	       "basic_close.sml", "eq_close.sml", "imp_close.sml",
	       "win_core.sml", "win.sml", "history.sml", "signal.sml",
	       "defined.sml", "inter.sml", "tty.sml", "tactic.sml",
	       "window.sml"],
    help    = ["defs/","entries/","thms/"],
    loaded  = "fn () => ()"};

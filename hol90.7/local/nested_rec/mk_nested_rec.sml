val nested_rec_lib =
 new_library
     {name = "nested_rec",
     doc = "Nested recursive type definition library, by H. Goguen and E. Gunter",
     path = (!HOLdir)^"contrib/nested_rec/",
     parents = [(Library.find_library "mutrec")],
     theories = [],
     code = ["gen_funs.sig","gen_funs.sml","exists_funs.sml", 
             "table.sig","table.sml","entries.sml", 
             "def_type.sig", "make_type_op.sml", "def_type.sml",
             "nested_rec_def.sml"],
     help = [],
     loaded = "fn () => ()"};

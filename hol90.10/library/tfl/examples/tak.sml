new_theory"tak" handle _ => ();

val {rules,WFthm,prim_eqns} = Rfunction
`measure \(x,y,z). x+y+z`
`tak(x,y,z) = (x<=y => z | tak(tak(x-1,y,z),tak(y-1,z,x),tak(z-1,x,y)))`;

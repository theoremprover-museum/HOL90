(* Fortenbacher's tests *)
(*1*)
val a = --`0 + x`--
and b = --`1 + y`--
(*2*)
and c = --`x + x`-- 
and d = --`y + z`--
(*3*)
and e = --`(x + x) + ((y + 0) + 2)`--
and f = --`1 + (1 + (z + 2))`--
(*4*)
and g = --`(x + 0) * ((y + 0) * (2 * 2))`--
and h = --`(z + (z + z)) * w`--
(*5*)
and i = --`((x + 0) * (y + 0)) * (z + 0)`--
and j = --`((w + (w + w)) * z) * z`--
(*6*)
and k = --`x * ((0 * x) * 0)`--
and l = --`(SUC y) * ((SUC 0) * (z * z))`--;


local 
val ACs = [--`+`--, --`*`--]
in
  fun U tm1 tm2 = Ac_tools.Acu.hol_ac_unify ACs tm1 tm2
  fun M tm1 tm2 = Ac_tools.Acu.hol_ac_match ACs tm1 tm2
end;


U a b;
U c d;
U e f;
U g h;
U i j;
U k l;

(*-------------------------------------------------------------------------- *)
(* Tests from the "AC-unification Race" paper *)

val ACs = [--`+`--]
val mk_AC  = fn flist => Ac_tools.Acu.Ac_term.mk_ac ACs (--flist--) 
val unify = Ac_tools.Acu.ac_unify ACs

(* 2 solutions *)
val t1l = mk_AC `(x + (0 + 1))`;
val t1r = mk_AC `(y + (2 + (3 + 4)))`;
length (unify t1l t1r) = 2;

(* 2 solutions *)
val t2l = mk_AC `(x + (0 + 1))`;
val t2r = mk_AC `(y + (2 + (2 + 3)))`;
length (unify t2l t2r) = 2;

(* 2 solutions *)
val t3l = mk_AC `(x + (0 + 1))`;
val t3r = mk_AC `(y + (2 + (2 + 2)))`;
length (unify t3l t3r) = 2;

(* 12 solutions *)
val t4l = mk_AC `(x + (0 + 1))`;
val t4r = mk_AC `(y + (z + (2 + 3)))`;
length (unify t4l t4r) = 12;

(* 12 solutions *)
val t5l = mk_AC `(x + (0 + 1))`;
val t5r = mk_AC `(y + (z + (2 + 2)))`;
length (unify t5l t5r) = 12;

(* 30 solutions *)
val t6l = mk_AC `(x + (0 + 1))`;
val t6r = mk_AC `(y + (z + (u + 2)))`;
length (unify t6l t6r) = 30;

(* 56 solutions *)
val t7l = mk_AC `(x + (0 + 1))`;
val t7r = mk_AC `(y + (z + (u + v)))`;
length (unify t7l t7r) = 56;

(* 2 solutions *)
val t8l = mk_AC `(x + (0 + 1))`;
val t8r = mk_AC `(y + (y + (2 + 3)))`;
length (unify t8l t8r) = 2;

(* 2 solutions *)
val t9l = mk_AC `(x + (0 + 1))`;
val t9r = mk_AC `(y + (y + (2 + 2)))`;
length (unify t9l t9r) = 2;

(* 12 solutions *)
val t10l = mk_AC `(x + (0 + 1))`;
val t10r = mk_AC `(y + (y + (z + 2)))`;
length (unify t10l t10r) = 12;

(* 30 solutions *)
val t11l = mk_AC `(x + (0 + 1))`;
val t11r = mk_AC `(y + (y + (z + u)))`;
length (unify t11l t11r) = 30;

(* 12 solutions *)
val t12l = mk_AC `(x + (0 + 1))`;
val t12r = mk_AC `(y + (y + (z + z)))`;
length (unify t12l t12r) = 12;

(* 2 solutions *)
val t13l = mk_AC `(x + (0 + 1))`;
val t13r = mk_AC `(y + (y + (y + 2)))`;
length (unify t13l t13r) = 2;

(* 12 solutions *)
val t14l = mk_AC `(x + (0 + 1))`;
val t14r = mk_AC `(y + (y + (y + z)))`;
length (unify t14l t14r) = 12;

(* 2 solutions *)
val t15l = mk_AC `(x + (0 + 1))`;
val t15r = mk_AC `(y + (y + (y + y)))`;
length (unify t15l t15r) = 2;

(*=========================================================*)

(* 2 solutions *)
val t16l = mk_AC `(x + (0 + 0))`;
val t16r = mk_AC `(y + (2 + (3 + 4)))`;
length (unify t16l t16r) = 2;

(* 2 solutions *)
val t17l = mk_AC `(x + (0 + 0))`;
val t17r = mk_AC `(y + (2 + (2 + 3)))`;
length (unify t17l t17r) = 2;

(* 2 solutions *)
val t18l = mk_AC `(x + (0 + 0))`;
val t18r = mk_AC `(y + (2 + (2 + 2)))`;
length (unify t18l t18r) = 2;

(* 8 solutions *)
val t19l = mk_AC `(x + (0 + 0))`;
val t19r = mk_AC `(y + (z + (2 + 3)))`;
length (unify t19l t19r) = 8;

(* 8 solutions *)
val t20l = mk_AC `(x + (0 + 0))`;
val t20r = mk_AC `(y + (z + (2 + 2)))`;
length (unify t20l t20r) = 8;

(* 18 solutions *)
val t21l = mk_AC `(x + (0 + 0))`;
val t21r = mk_AC `(y + (z + (u + 2)))`;
length (unify t21l t21r) = 18;

(* 32 solutions *)
val t22l = mk_AC `(x + (0 + 0))`;
val t22r = mk_AC `(y + (z + (u + v)))`;
length (unify t22l t22r) = 32;

(* 2 solutions *)
val t23l = mk_AC `(x + (0 + 0))`;
val t23r = mk_AC `(y + (y + (2 + 3)))`;
length (unify t23l t23r) = 2;

(* 2 solutions *)
val t24l = mk_AC `(x + (0 + 0))`;
val t24r = mk_AC `(y + (y + (2 + 2)))`;
length (unify t24l t24r) = 2;

(* 4 solutions *)
val t25l = mk_AC `(x + (0 + 0))`;
val t25r = mk_AC `(y + (y + (z + 2)))`;
length (unify t25l t25r) = 4;

(* 10 solutions *)
val t26l = mk_AC `(x + (0 + 0))`;
val t26r = mk_AC `(y + (y + (z + u)))`;
length (unify t26l t26r) = 10;

(* 4 solutions *)
val t27l = mk_AC `(x + (0 + 0))`;
val t27r = mk_AC `(y + (y + (z + z)))`;
length (unify t27l t27r) = 4;

(* 2 solutions *)
val t28l = mk_AC `(x + (0 + 0))`;
val t28r = mk_AC `(y + (y + (y + 2)))`;
length (unify t28l t28r) = 2;

(* 4 solutions *)
val t29l = mk_AC `(x + (0 + 0))`;
val t29r = mk_AC `(y + (y + (y + z)))`;
length (unify t29l t29r) = 4;

(* 2 solutions *)
val t30l = mk_AC `(x + (0 + 0))`;
val t30r = mk_AC `(y + (y + (y + y)))`;
length (unify t30l t30r) = 2;

(*=======================================================*)

(* 28 solutions *)
val t31l = mk_AC `(x + (y + 0))`;
val t31r = mk_AC `(z + (2 + (3 + 4)))`;
length (unify t31l t31r) = 28;

(* 20 solutions *)
val t32l = mk_AC `(x + (y + 0))`;
val t32r = mk_AC `(z + (2 + (2 + 3)))`;
length (unify t32l t32r) = 20;

(* 12 solutions *)
val t33l = mk_AC `(x + (y + 0))`;
val t33r = mk_AC `(z + (2 + (2 + 2)))`;
length (unify t33l t33r) = 12;

(* 88 solutions *)
val t34l = mk_AC `(x + (y + 0))`;
val t34r = mk_AC `(z + (u + (2 + 3)))`;
length (unify t34l t34r) = 88;

(* 64 solutions *)
val t35l = mk_AC `(x + (y + 0))`;
val t35r = mk_AC `(z + (u + (2 + 2)))`;
length (unify t35l t35r) = 64;

(* 204 solutions *)
val t36l = mk_AC `(x + (y + 0))`;
val t36r = mk_AC `(z + (u + (v + 2)))`;
length (unify t36l t36r) = 204;

(* 416 solutions *)
val t37l = mk_AC `(x + (y + 0))`;
val t37r = mk_AC `(z + (u + (v + w)))`;
length (unify t37l t37r) = 416;

(* 60 solutions *)
val t38l = mk_AC `(x + (y + 0))`;
val t38r = mk_AC `(z + (z + (2 + 3)))`;
length (unify t38l t38r) = 60;

(* 44 solutions *)
val t39l = mk_AC `(x + (y + 0))`;
val t39r = mk_AC `(z + (z + (2 + 2)))`;
length (unify t39l t39r) = 44;

(* 144 solutions *)
val t40l = mk_AC `(x + (y + 0))`;
val t40r = mk_AC `(z + (z + (u + 2)))`;
length (unify t40l t40r) = 144;

(* 300 solutions *)
val t41l = mk_AC `(x + (y + 0))`;
val t41r = mk_AC `(z + (z + (u + v)))`;
length (unify t41l t41r) = 300;

(* 216 solutions *)
val t42l = mk_AC `(x + (y + 0))`;
val t42r = mk_AC `(z + (z + (u + u)))`;
length (unify t42l t42r) = 216;

(* 92 solutions *)
val t43l = mk_AC `(x + (y + 0))`;
val t43r = mk_AC `(z + (z + (z + 2)))`;
length (unify t43l t43r) = 92;

(* 196 solutions *)
val t44l = mk_AC `(x + (y + 0))`;
val t44r = mk_AC `(z + (z + (z + u)))`;
length (unify t44l t44r) = 196;

(* 124 solutions *)
val t45l = mk_AC `(x + (y + 0))`;
val t45r = mk_AC `(z + (z + (z + z)))`;
length (unify t45l t45r) = 124;

(*=====================================================
  =====================================================*)

(* 120 solutions *)
val t46l = mk_AC `(x + (y + z))`;
val t46r = mk_AC `(u + (2 + (3 + 4)))`;
length (unify t46l t46r) = 120;

(* 75 solutions *)
val t47l = mk_AC `(x + (y + z))`;
val t47r = mk_AC `(u + (2 + (2 + 3)))`;
length (unify t47l t47r) = 75;

(* 37 solutions *)
val t48l = mk_AC `(x + (y + z))`;
val t48r = mk_AC `(u + (2 + (2 + 2)))`;
length (unify t48l t48r) = 37;

(* 336 solutions *)
val t49l = mk_AC `(x + (y + z))`;
val t49r = mk_AC `(u + (v + (2 + 3)))`;
length (unify t49l t49r) = 336;

(* 216 solutions *)
val t50l = mk_AC `(x + (y + z))`;
val t50r = mk_AC `(u + (v + (2 + 2)))`;
length (unify t50l t50r) = 216;

(* 870 solutions *)
val t51l = mk_AC `(x + (y + z))`;
val t51r = mk_AC `(u + (v + (w + 2)))`;
length (unify t51l t51r) = 870;

(* 2161 solutions *)
val t52l = mk_AC `(x + (y + z))`;
val t52r = mk_AC `(u + (v + (w + t)))`;
length (unify t52l t52r) = 2161;

(* 486 solutions *)
val t53l = mk_AC `(x + (y + z))`;
val t53r = mk_AC `(u + (u + (2 + 3)))`;
length (unify t53l t53r) = 486;

(* 318 solutions *)
val t54l = mk_AC `(x + (y + z))`;
val t54r = mk_AC `(u + (u + (2 + 2)))`;
length (unify t54l t54r) = 318;

(* 1200 solutions *)
val t55l = mk_AC `(x + (y + z))`;
val t55r = mk_AC `(u + (u + (v + 2)))`;
length (unify t55l t55r) = 1200;

(* 2901 solutions *)
val t56l = mk_AC `(x + (y + z))`;
val t56r = mk_AC `(u + (u + (v + w)))`;
length (unify t56l t56r) = 2901;

(* 3825 solutions *)
val t57l = mk_AC `(x + (y + z))`;
val t57r = mk_AC `(u + (u + (v + v)))`;
length (unify t57l t57r) = 3825;

(* 2982 solutions *)
val t58l = mk_AC `(x + (y + z))`;
val t58r = mk_AC `(u + (u + (u + 2)))`;
length (unify t58l t58r) = 2982;

(* 7029 solutions,  *)
val t59l = mk_AC `(x + (y + z))`;
val t59r = mk_AC `(u + (u + (u + v)))`;
length (unify t59l t59r) = 7029;

(* 32677 solutions 
val t60l = mk_AC `(x + (y + z))`;
val t60r = mk_AC `(u + (u + (u + u)))`;
*)

(*====================================================*)

(* 2 solutions *)
val t61l = mk_AC `(x + (x + 0))`;
val t61r = mk_AC `(y + (2 + (3 + 4)))`;
length (unify t61l t61r) = 2;

(* 2 solutions *)
val t62l = mk_AC `(x + (x + 0))`;
val t62r = mk_AC `(y + (2 + (2 + 3)))`;
length (unify t62l t62r) = 2;

(* 2 solutions *)
val t63l = mk_AC `(x + (x + 0))`;
val t63r = mk_AC `(y + (2 + (3 + 4)))`;
length (unify t63l t63r) = 2;

(* 60 solutions *)
val t64l = mk_AC `(x + (x + 0))`;
val t64r = mk_AC `(y + (z + (2 + 3)))`;
length (unify t64l t64r) = 60;

(* 12 solutions *)
val t65l = mk_AC `(x + (x + 0))`;
val t65r = mk_AC `(y + (z + (2 + 2)))`;
length (unify t65l t65r) = 12;

(* 486 solutions *)
val t66l = mk_AC `(x + (x + 0))`;
val t66r = mk_AC `(y + (z + (u + 2)))`;
length (unify t66l t66r) = 486;

(* 3416 solutions *)
val t67l = mk_AC `(x + (x + 0))`;
val t67r = mk_AC `(y + (z + (u + v)))`;
length (unify t67l t67r) = 3416;

(* 0 solutions *)
val t68l = mk_AC `(x + (x + 0))`;
val t68r = mk_AC `(y + (y + (2 + 3)))`;
length (unify t68l t68r) = 0;

(* 0 solutions *)
val t69l = mk_AC `(x + (x + 0))`;
val t69r = mk_AC `(y + (y + (2 + 2)))`;
length (unify t69l t69r) = 0;

(* 2 solutions *)
val t70l = mk_AC `(x + (x + 0))`;
val t70r = mk_AC `(y + (y + (z + 2)))`;
length (unify t70l t70r) = 2;

(* 12 solutions *)
val t71l = mk_AC `(x + (x + 0))`;
val t71r = mk_AC `(y + (y + (z + u)))`;
length (unify t71l t71r) = 12;

(* 0 solutions *)
val t72l = mk_AC `(x + (x + 0))`;
val t72r = mk_AC `(y + (y + (z + z)))`;
length (unify t72l t72r) = 0;

(* 2 solutions *)
val t73l = mk_AC `(x + (x + 0))`;
val t73r = mk_AC `(y + (y + (y + 2)))`;
length (unify t73l t73r) = 2;

(* 12 solutions *)
val t74l = mk_AC `(x + (x + 0))`;
val t74r = mk_AC `(y + (y + (y + z)))`;
length (unify t74l t74r) = 12;

(* 0 solutions *)
val t75l = mk_AC `(x + (x + 0))`;
val t75r = mk_AC `(y + (y + (y + y)))`;
length (unify t75l t75r) = 0;

(*==================================================*)

(* 28 solutions *)
val t76l = mk_AC `(x + (x + y))`;
val t76r = mk_AC `(z + (2 + (3 + 4)))`;
length (unify t76l t76r) = 28;

(* 11 solutions *)
val t77l = mk_AC `(x + (x + y))`;
val t77r = mk_AC `(z + (2 + (2 + 3)))`;
length (unify t77l t77r) = 11;

(* 7 solutions *)
val t78l = mk_AC `(x + (x + y))`;
val t78r = mk_AC `(z + (2 + (2 + 2)))`;
length (unify t78l t78r) = 7;

(* 228 solutions *)
val t79l = mk_AC `(x + (x + y))`;
val t79r = mk_AC `(z + (u + (2 + 3)))`;
length (unify t79l t79r) = 228;

(* 44 solutions *)
val t80l = mk_AC `(x + (x + y))`;
val t80r = mk_AC `(z + (u + (2 + 2)))`;
length (unify t80l t80r) = 44;

(* 1632 solutions *)
val t81l = mk_AC `(x + (x + y))`;
val t81r = mk_AC `(z + (u + (v + 2)))`;
length (unify t81l t81r) = 1632;

(* 13703 solutions  -- slow *)
val t82l = mk_AC `(x + (x + y))`;
val t82r = mk_AC `(z + (u + (v + w)))`;


(* 2 solutions *)
val t83l = mk_AC `(x + (x + y))`;
val t83r = mk_AC `(z + (z + (2 + 3)))`;
length (unify t83l t83r) = 2;

(* 4 solutions *)
val t84l = mk_AC `(x + (x + y))`;
val t84r = mk_AC `(z + (z + (2 + 2)))`;
length (unify t84l t84r) = 4;

(* 18 solutions *)
val t85l = mk_AC `(x + (x + y))`;
val t85r = mk_AC `(z + (z + (u + 2)))`;
length (unify t85l t85r) = 18;

(* 69 solutions *)
val t86l = mk_AC `(x + (x + y))`;
val t86r = mk_AC `(z + (z + (u + v)))`;
length (unify t86l t86r) = 69;

(* 7 solutions *)
val t87l = mk_AC `(x + (x + y))`;
val t87r = mk_AC `(z + (z + (u + u)))`;
length (unify t87l t87r) = 7;

(* 12 solutions *)
val t88l = mk_AC `(x + (x + y))`;
val t88r = mk_AC `(z + (z + (z + 2)))`;
length (unify t88l t88r) = 12;

(* 47 solutions *)
val t89l = mk_AC `(x + (x + y))`;
val t89r = mk_AC `(z + (z + (z + u)))`;
length (unify t89l t89r) = 47;

(* 5 solutions *)
val t90l = mk_AC `(x + (x + y))`;
val t90r = mk_AC `(z + (z + (z + z)))`;
length (unify t90l t90r) = 5;

(*==================================================*)

(* 2 solutions *)
val t91l = mk_AC `(x + (x + x))`;
val t91r = mk_AC `(y + (2 + (3 + 4)))`;
length (unify t91l t91r) = 2;

(* 2 solutions *)
val t92l = mk_AC `(x + (x + x))`;
val t92r = mk_AC `(y + (2 + (2 + 3)))`;
length (unify t92l t92r) = 2;

(* 1 solutions *)
val t93l = mk_AC `(x + (x + x))`;
val t93r = mk_AC `(y + (2 + (2 + 2)))`;
length (unify t93l t93r) = 1;

(* 140 solutions *)
val t94l = mk_AC `(x + (x + x))`;
val t94r = mk_AC `(y + (z + (2 + 3)))`;
length (unify t94l t94r) = 140;

(* 28 solutions *)
val t95l = mk_AC `(x + (x + x))`;
val t95r = mk_AC `(y + (z + (2 + 2)))`;
length (unify t95l t95r) = 28;

(* 6006 solutions *)
val t96l = mk_AC `(x + (x + x))`;
val t96r = mk_AC `(y + (z + (u + 2)))`;
length (unify t96l t96r) = 6006;

(* 1,044,569 solutions  -- not attempted
val t97l = mk_AC `(x + (x + x))`;
val t97r = mk_AC `(y + (z + (u + v)))`;
*)

(* 2 solutions *)
val t98l = mk_AC `(x + (x + x))`;
val t98r = mk_AC `(y + (y + (2 + 3)))`;
length (unify t98l t98r) = 2;

(* 2 solutions *)
val t99l = mk_AC `(x + (x + x))`;
val t99r = mk_AC `(y + (y + (2 + 2)))`;
length (unify t99l t99r) = 2;

(* 12 solutions *)
val t100l = mk_AC `(x + (x + x))`;
val t100r = mk_AC `(y + (y + (z + 2)))`;
length (unify t100l t100r) = 12;

(* 101 solutions *)
val t101l = mk_AC `(x + (x + x))`;
val t101r = mk_AC `(y + (y + (z + u)))`;
length (unify t101l t101r) = 101;

(* 13 solutions *)
val t102l = mk_AC `(x + (x + x))`;
val t102r = mk_AC `(y + (y + (z + z)))`;
length (unify t102l t102r) = 13;

(* 0 solutions *)
val t103l = mk_AC `(x + (x + x))`;
val t103r = mk_AC `(y + (y + (y + 2)))`;
length (unify t103l t103r) = 0;

(* 1 solution *)
val t104l = mk_AC `(x + (x + x))`;
val t104r = mk_AC `(y + (y + (y + z)))`;
length (unify t104l t104r) = 1;

(* 1 solution *)
val t105l = mk_AC `(x + (x + x))`;
val t105r = mk_AC `(y + (y + (y + y)))`;
length (unify t105l t105r) = 1;

# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: CSP
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories and compile code
#
# make clean	    : remove theories and compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# outofbox_Hol : the pathname of the stock version of hol used
# Hol          : the pathname of the version of hol with libraries loaded
# =====================================================================
outofbox_Hol=hol90
Hol=./CSP_hol
Theory_dir=../ascii

clean:
	rm -f *.holsig *.log *.thms ${Theory_dir}/* ${Hol}
	@echo "===> library csp: all object code and theory files deleted"  

.SUFFIXES: .thms .sml

.sml.thms:;	/bin/rm -f $*.thms $*.holsig $*.log
		echo 'use "$*.sml";'\
                     'print_theory "-";'\
                     'exit();' | ${Hol} > $*.log 2>&1

CSP_hol:
	echo 'use "mk_csp_base.sml";' | ${outofbox_Hol}

all:	CSP_hol\
	boolarith1.thms boolarith2.thms list_lib1.thms\
	traces.thms restrict.thms star.thms order.thms\
	process_ty.thms\
	stop.thms run.thms prefix.thms after.thms choice.thms parallel.thms\
	process_fix.thms mu.thms process.thms\
	after_laws.thms par_laws.thms\
	csp_syntax.thms\
	CSP.thms
	@echo "===> library csp rebuilt"

boolarith1.thms: boolarith1.sml CSP_hol

boolarith2.thms: boolarith2.sml boolarith1.thms CSP_hol

list_lib1.thms: list_lib1.sml CSP_hol

traces.thms: traces.sml list_lib1.thms CSP_hol

restrict.thms: restrict.sml traces.thms boolarith2.thms CSP_hol

star.thms: star.sml restrict.thms CSP_hol

order.thms: order.sml restrict.thms CSP_hol

process_ty.thms: process_ty.sml star.thms CSP_hol
 
stop.thms: stop.sml process_ty.thms CSP_hol
 
run.thms: run.sml process_ty.thms CSP_hol
 
prefix.thms: prefix.sml process_ty.thms CSP_hol
 
after.thms: after.sml process_ty.thms CSP_hol
 
choice.thms: choice.sml process_ty.thms CSP_hol

parallel.thms: parallel.sml process_ty.thms CSP_hol

process_fix.thms: process_fix.sml stop.thms CSP_hol

mu.thms: mu.sml process_fix.thms CSP_hol

process.thms: process.sml run.thms prefix.thms choice.thms after.thms parallel.thms mu.thms CSP_hol

after_laws.thms: after_laws.sml process.thms CSP_hol

par_laws.thms: par_laws.sml process.thms CSP_hol

csp_syntax.thms: csp_syntax.sml process.thms CSP_hol

CSP.thms: CSP.sml csp_syntax.thms after_laws.thms par_laws.thms order.thms CSP_hol

# For simpletons like me: the following will rebuild the system.
#
# CSP_hol < boolarith1.sml
# CSP_hol < boolarith2.sml
# CSP_hol < list_lib1.sml
# CSP_hol < traces.sml
# CSP_hol < restrict.sml
# CSP_hol < star.sml
# CSP_hol < order.sml
# CSP_hol < process_ty.sml
# CSP_hol < stop.sml
# CSP_hol < run.sml
# CSP_hol < prefix.sml
# CSP_hol < after.sml
# CSP_hol < choice.sml
# CSP_hol < parallel.sml
# CSP_hol < process_fix.sml
# CSP_hol < mu.sml
# CSP_hol < process.sml
# CSP_hol < after_laws.sml
# CSP_hol < par_laws.sml
# CSP_hol < csp_syntax.sml
# CSP_hol < CSP.sml


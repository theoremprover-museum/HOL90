# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: window
#
# $Id: Makefile,v 4.1 1994/09/10 03:27:58 jim Exp $
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : make the source and theory files.
#
#    make source    : check out the source code (see REVISION)
#
#    make install   : make the source and theories and define the
#                     library.
#
#    make clean	    : remove the theories.
#	
#    make clobber   : remove theories, and source code that isn't
#                     different to that in REVISION.
#
# ---------------------------------------------------------------------
# MACROS:
#
#    HOL            : the pathname of the version of hol used
#    SOURCE         : all the source files
#    REVISION       : The rcs revision of the source code to get
# =====================================================================

HOL=hol90.7

SOURCE=src/basic_close.sml src/defined.sml src/eq_close.sml		\
      src/history.sml src/hol_ext.sml src/imp_close.sml src/inter.sml	\
      src/ml_ext.sml src/relations.sml src/rules.sml src/signal.sml	\
      src/tactic.sml src/tty.sml src/win.sml src/win_core.sml src/window.sml

REVISION=

# =====================================================================
# Basic functions.
# =====================================================================

all: source theories
	@echo "===> library window built"

install: all install.sml
	${HOL} < install.sml
	@echo "===> library window installed"

source: ${SOURCE}
	@echo "===> library window source code built"

theories: theories/ascii/window.holsig theories/ascii/window.thms
	@echo "===> library window theories built"

theories/ascii/window.holsig theories/ascii/window.thms:	\
		theories/src/mk_window.sml
	cd theories/src; ${HOL} < mk_window.sml
	mv theories/src/window.holsig theories/ascii/window.holsig
	mv theories/src/window.thms theories/ascii/window.thms

clean:
	rm -f theories/ascii/window.holsig theories/ascii/window.thms
	@echo "===> library window: all theory files deleted"

clobber: clean
	rcsclean -r${REVISION} ${SOURCE}
	rcsclean -r${REVISION} install.sml make_window
	rcsclean -r${REVISION} theories/src/mk_window.sml
	@echo "===> library window: all source code deleted"

.FAILED:
	@echo "===> library window build failed"

.DEFAULT:
	co -r${REVISION} $@

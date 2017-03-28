#-------------------------------------------------------------------------
# Makefile for HOL90
#-------------------------------------------------------------------------

HOL90_VERSION=10

#-------------------------------------------------------------------------
# parameters
#-------------------------------------------------------------------------

SML_IMPL=njsml.1xx
ARCH=unknown
#HOL_DIR:sh=(cd ../..; /bin/pwd) # works on Suns
HOL_DIR=../..
THEORY_TYPE=ascii

#LIBRARIES=lite ho_match refute fol tab meson decision reduce arith simp\
#	  automate ind_def_new tfl\
#	  string option num set pred_set unwind hol88 ind_def taut utils\
#	  retrieve group integer abs_theory unity prog_logic pair real\
#	  wellorder window list res_quan word

LIBRARIES=lite ho_match refute fol tab meson decision reduce arith simp\
	  ind_def_new tfl\
	  string option num set pred_set unwind hol88 ind_def taut utils\
	  retrieve group integer abs_theory unity prog_logic pair real\
	  wellorder window list res_quan word

CONTRIBS=`/bin/ls ../contrib`

# Libraries to load before dumping HOL executable/heap/database
#PRE_LOAD=automate ind_def_new
PRE_LOAD=

# File to `use' before dumping HOL executable/heap/database
USE_FILE=

LEX=flex
LEX_LIB=fl
CC=gcc

#-------------------------------------------------------------------------
# computed macros
#-------------------------------------------------------------------------
SRC_DIR=$(HOL_DIR)/src
BIN_DIR=$(HOL_DIR)/bin
THEORY_SRC=$(HOL_DIR)/theories/src
THMS_DIR=$(HOL_DIR)/theories/$(THEORY_TYPE)
HOLSIG_DIR=$(HOL_DIR)/theories/$(THEORY_TYPE)
LIBRARY_DIR=$(HOL_DIR)/library
CONTRIB_DIR=$(HOL_DIR)/contrib

PIPE=$(BIN_DIR)/pipe

#-------------------------------------------------------------------------
# all
#-------------------------------------------------------------------------

all: pipe filter hol hol-script library

#-------------------------------------------------------------------------
# pipe
#
# A shell script to allow a file to be piped through the filter without an
# explicit pipe having to appear in the command executed by the SML
# process.
#-------------------------------------------------------------------------

pipe: $(PIPE)

$(PIPE):
	@-mkdir $(BIN_DIR) 2> /dev/null
	echo '#!/bin/sh' > $@
	echo '/bin/cat $$1 | $$2' >> $@
	chmod a+rx $@

#-------------------------------------------------------------------------
# filter
#-------------------------------------------------------------------------

filter: $(BIN_DIR)/quote-filter.$(ARCH)

$(BIN_DIR)/quote-filter.$(ARCH): $(SRC_DIR)/quote-filter/filter.lex
	@-mkdir $(BIN_DIR) 2> /dev/null
	$(LEX) -t $(SRC_DIR)/quote-filter/filter.lex >/tmp/lex.yy.c
	$(CC) -o $@ /tmp/lex.yy.c -l$(LEX_LIB)
	rm /tmp/lex.yy.c
	chmod a+rx $@

#-------------------------------------------------------------------------
# hol
#-------------------------------------------------------------------------

hol: pipe filter hol-script
	@-mkdir $(BIN_DIR) 2> /dev/null
	@-mkdir $(LIBRARY_DIR)/desc 2> /dev/null
	$(MAKE) -f $(SRC_DIR)/Makefiles/$(SML_IMPL) \
	        HOL90_VERSION=$(HOL90_VERSION) \
		ARCH=$(ARCH) \
	        HOL_DIR=$(HOL_DIR) \
	        THEORY_TYPE=$(THEORY_TYPE) \
	        PRE_LOAD="$(PRE_LOAD)" \
	        USE_FILE=$(USE_FILE)

#-------------------------------------------------------------------------
# hol-script
#-------------------------------------------------------------------------

hol-script:
	@-mkdir $(BIN_DIR) 2> /dev/null
	echo '#!/bin/sh' > $(BIN_DIR)/hol90
	echo holdir=$(HOL_DIR) >> $(BIN_DIR)/hol90
	echo version=$(HOL90_VERSION) >> $(BIN_DIR)/hol90
	echo sml=$(SML_IMPL) >> $(BIN_DIR)/hol90
	cat script >> $(BIN_DIR)/hol90
	chmod a+rx $(BIN_DIR)/hol90

$(BIN_DIR)/hol90: $(SRC_DIR)/script
	$(MAKE) hol-script \
	        HOL90_VERSION=$(HOL90_VERSION) \
	        SML_IMPL=$(SML_IMPL) \
	        HOL_DIR=$(HOL_DIR)

#-------------------------------------------------------------------------
# library
#-------------------------------------------------------------------------

library: hol $(BIN_DIR)/hol90 
	@echo "=====> Making system libraries"
	@THEORY_TYPE=$(THEORY_TYPE); export THEORY_TYPE;\
	for lib in $(LIBRARIES);\
	do if test -d $(LIBRARY_DIR)/$$lib;\
	   then if test -f $(LIBRARY_DIR)/$$lib/make_$$lib;\
	        then (echo Making the $$lib library;\
	              cd $(LIBRARY_DIR)/$$lib;\
	              ./make_$$lib $(BIN_DIR)/hol90 -ml $(SML_IMPL);\
	              echo "=====> The $$lib library is made.");\
	        else echo No make file found for library $$lib;\
	        fi;\
	   else echo Library $$lib not found;\
	   fi;\
	done

library_test: library
	@echo "=====> Testing system libraries"
	for lib in $(LIBRARIES);\
	do (echo Loading the $$lib library;\
            echo "load_library{lib = $$(lib)_lib,theory=\"foo\"};"\
              | $(BIN_DIR)/hol90 -ml $(SML_IMPL);\
            echo "=====> The $$lib library loads.");\
	done


#-------------------------------------------------------------------------
# contrib
#-------------------------------------------------------------------------

contrib: hol $(BIN_DIR)/hol90
	@echo "=====> Making contributed libraries"
	@THEORY_TYPE=$(THEORY_TYPE); export THEORY_TYPE;\
	 for lib in $(CONTRIBS);\
	 do if test -d $(CONTRIB_DIR)/$$lib -a $$lib != "desc";\
	    then if test -f $(CONTRIB_DIR)/$$lib/make_$$lib;\
	         then (echo Making the $$lib contributed library;\
	               cd $(CONTRIB_DIR)/$$lib;\
	               ./make_$$lib $(BIN_DIR)/hol90 -ml $(SML_IMPL);\
	               echo "=====> The $$lib contributed library is made");\
	         else echo No make file found for contributed library $$lib;\
	         fi;\
	    fi;\
	 done

#-------------------------------------------------------------------------
# cleaning
#-------------------------------------------------------------------------

clean:
	$(MAKE) clean -f Makefiles/$(SML_IMPL) \
	        HOL90_VERSION=$(HOL90_VERSION) \
		ARCH=$(ARCH) \
	        HOL_DIR=$(HOL_DIR) \
	        THEORY_TYPE=$(THEORY_TYPE)

lib_clean:
	$(MAKE) lib_clean -f Makefiles/$(SML_IMPL) \
		HOL90_VERSION=$(HOL90_VERSION) \
		ARCH=$(ARCH) \
	        HOL_DIR=$(HOL_DIR) \
	        THEORY_TYPE=$(THEORY_TYPE)

contrib_clean:
	rm -f $(CONTRIB_DIR)/desc/*.hol_lib
	@echo "=====> Removed old descriptions"

clobber: clean
	rm -f $(HOLSIG_DIR)/*.holsig $(THMS_DIR)/*.thms


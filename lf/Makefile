#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.4pl6     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f _CoqProject AutoTest.v Auto.v BasicsTest.v Basics.v BibTest.v Bib.v ExtractionTest.v Extraction.v ImpCEvalFunTest.v ImpCEvalFun.v ImpParserTest.v ImpParser.v ImpTest.v Imp.v IndPrinciplesTest.v IndPrinciples.v IndPropTest.v IndProp.v InductionTest.v Induction.v ListsTest.v Lists.v LogicTest.v Logic.v MapsTest.v Maps.v PolyTest.v Poly.v PostscriptTest.v Postscript.v PrefaceTest.v Preface.v ProofObjectsTest.v ProofObjects.v RelTest.v Rel.v TacticsTest.v Tactics.v -o Makefile 
#

.DEFAULT_GOAL := all

# 
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?=-I . 
COQDOCLIBS?=

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?="$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=AutoTest.v\
  Auto.v\
  BasicsTest.v\
  Basics.v\
  BibTest.v\
  Bib.v\
  ExtractionTest.v\
  Extraction.v\
  ImpCEvalFunTest.v\
  ImpCEvalFun.v\
  ImpParserTest.v\
  ImpParser.v\
  ImpTest.v\
  Imp.v\
  IndPrinciplesTest.v\
  IndPrinciples.v\
  IndPropTest.v\
  IndProp.v\
  InductionTest.v\
  Induction.v\
  ListsTest.v\
  Lists.v\
  LogicTest.v\
  Logic.v\
  MapsTest.v\
  Maps.v\
  PolyTest.v\
  Poly.v\
  PostscriptTest.v\
  Postscript.v\
  PrefaceTest.v\
  Preface.v\
  ProofObjectsTest.v\
  ProofObjects.v\
  RelTest.v\
  Rel.v\
  TacticsTest.v\
  Tactics.v

-include $(addsuffix .d,$(VFILES))
.SECONDARY: $(addsuffix .d,$(VFILES))

VOFILES:=$(VFILES:.v=.vo)
VOFILESINC=$(filter $(wildcard ./*),$(VOFILES)) 
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) ./LF\
  ./.\
  ./-Q

spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all opt byte archclean clean install userinstall depend html validate ./LF ./. ./-Q

###################
#                 #
# Subdirectories. #
#                 #
###################

./LF:
	cd ./LF ; $(MAKE) all

./.:
	cd ./. ; $(MAKE) all

./-Q:
	cd ./-Q ; $(MAKE) all

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install:
	install -d $(DSTROOT)$(COQLIBINSTALL)/$(INSTALLDEFAULTROOT); \
	for i in $(VOFILESINC); do \
	 install -m 0644 $$i $(DSTROOT)$(COQLIBINSTALL)/$(INSTALLDEFAULTROOT)/`basename $$i`; \
	done
	+cd ./LF && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./LF" install
	+cd ./. && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./." install
	+cd ./-Q && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./-Q" install

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/$$i;\
	done

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml
	(cd ./LF ; $(MAKE) clean)
	(cd ./. ; $(MAKE) clean)
	(cd ./-Q ; $(MAKE) clean)

archclean:
	rm -f *.cmx *.o
	(cd ./LF ; $(MAKE) archclean)
	(cd ./. ; $(MAKE) archclean)
	(cd ./-Q ; $(MAKE) archclean)

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

Makefile: _CoqProject
	mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@

	(cd ./LF ; $(MAKE) Makefile)
	(cd ./. ; $(MAKE) Makefile)
	(cd ./-Q ; $(MAKE) Makefile)

###################
#                 #
# Implicit rules. #
#                 #
###################

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING


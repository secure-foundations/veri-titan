# Useful targets:
#
# - make
#    Runs verification and compilation
# - make ready-for-merge
#    Runs verifification and compilation and dep graph building
# - make verify
#    Runs only verification
# - make compile
#    Runs only compilation (WARN: No verification done)
# - make extract
#    Runs only extraction to cpp files (WARN: No verification done)
# - make ver-%
#    Verify specific file and its dependencies
# - make proc-%
#    Verify a single procedure
# - make initialize
#    Set up githooks properly for this repo to help keep things clean
# - make whitespace-cleanup
#    Clean up whitespace in all of the files in this repo
# - make dep.png
#    Create a nice dependency graph, along with colors to indicate state of verification
# - make syntax-check
#    Only perform syntax checking
# - make clean
#    Clean up temporaries and other files
# - make csharps
#    Debug target -- generate csharp files instead
#
# Useful parameters
#
# - DAFNY: Path to dafny executable
# - DAFNY_ADDITIONAL_ARGS: Additional arguments to pass to dafny
# - TIMELIMIT: Set a different default timelimit (default: 30s)
# - PROFILE: Turn on SMT profiling during verification

DAFNY?=dafny
DAFNY_ADDITIONAL_ARGS?=
DAFNY_DIR?=$(patsubst %/Binaries/,%,$(dir $(realpath $(shell which $(DAFNY)))))
DAFNY_SYNTAX_CHECK?=

TIMELIMIT?=

DAFNY_VERIFY := $(DAFNY) \
	/compile:0 \
	/allocated:3 \
	/nologo \
	/printVerifiedProceduresCount:0 \
	$(DAFNY_ADDITIONAL_ARGS)

ifneq ($(TIMELIMIT),)
  DAFNY_VERIFY += /timeLimit:$(TIMELIMIT)
endif

ifdef PROFILE
DAFNY_VERIFY += "/z3opt:smt.qi.profile=true" "/z3opt:smt.qi.profile_freq=100"
endif

ifdef NL
DAFNY_VERIFY += /noNLarith
endif

CXX:=clang++

CLEAR_FLYCHECK_FILES:=$(shell rm -f flycheck_*.dfy)
DFYs:=$(wildcard *.dfy)
VERs:=$(patsubst %.dfy,%-ver,$(DFYs))
VERfiles:=$(patsubst %.dfy,obj/%.dfy.ver,$(DFYs))
INPROGRESS_VERfiles:=$(patsubst %.dfy,obj/inprogress.%.dfy.ver,$(DFYs))
DOTOs:=$(patsubst %.dfy,obj/%.o,$(DFYs))
CPPs:=$(patsubst %.dfy,obj/%.cpp,$(DFYs))
CSs:=$(patsubst %.dfy,obj/%.cs,$(DFYs))
DOTHs:=$(wildcard *.h)

DAFNY_RUNTIME_DIR:=$(DAFNY_DIR)/Binaries

DAFNY_DEPS:= \
	$(DAFNY_RUNTIME_DIR)/Dafny.exe \
	$(DAFNY_RUNTIME_DIR)/DafnyPipeline.dll \
	$(DAFNY_RUNTIME_DIR)/DafnyRuntime.h

CXXFLAGS += \
	-std=c++14 \
	-Werror \
	-Wall \
	-Wextra \
	-Wpedantic \
	-Wno-unused-parameter \
	-Wno-implicitly-unsigned-literal \
	-Wno-unused-variable \
	-ferror-limit=5 \
	-I$(DAFNY_RUNTIME_DIR)

BOLD:="\033[1m"
RED:="\033[31m"
BRIGHTRED:="\033[1;31m"
RESET:="\033[0m"

all: verify compile

verify: $(VERs)

compile: extract $(DOTOs) obj/quicdafny.a

extract: $(CPPs)

clean-compile:
	@echo $(BOLD)"[+] Cleaning up compilation files"$(RESET)
	@rm -f $(DOTOs) $(CPPs)

clean-verify:
	@echo $(BOLD)"[+] Cleaning up verification files"$(RESET)
	@rm -f $(INPROGRESS_VERfiles) $(VERfiles)

clean-syntaxcheck:
	@echo $(BOLD)"[+] Cleaning up syntax-check files"$(RESET)
	@rm -f $(patsubst %,%syn,$(INPROGRESS_VERfiles) $(VERfiles))

clean: clean-compile clean-verify clean-syntaxcheck
	@echo $(BOLD)"[+] Removing obj/ directory"$(RESET)
	@rm -rf obj/
	@echo $(BOLD)"[+] Removing .depend"$(RESET)
	@rm -rf .depend

whitespace-cleanup:
	@echo $(BOLD)"[+] Cleaning up whitespace for all dafny files"$(RESET)
	@sed -i -E "s/[[:blank:]]*$$//" $(DFYs)

ifneq ($(DAFNY_SYNTAX_CHECK),)
%-ver: obj/%.dfy.versyn
	@true
else
%-ver: obj/%.dfy.ver
	@true
endif

.PRECIOUS: obj/%.dfy.ver

.PRECIOUS: obj/%.dfy.versyn

obj:
	@echo $(BOLD)"[+] Making $@/ directory"$(RESET)
	@mkdir $@

.PRECIOUS: obj

obj/%.dfy.ver: %.dfy | obj
	@echo $(BOLD)"[+] Verifying $<"$(RESET)
	@touch $(dir $@)inprogress.$(notdir $@) && $(DAFNY_VERIFY) $< && touch $@ && rm -f $(dir $@)inprogress.$(notdir $@)

obj/%.dfy.versyn: %.dfy | obj
	@echo $(BOLD)"[+] Syntax checking $<"$(RESET)
	@touch $(dir $@)inprogress.$(notdir $@) && $(DAFNY_VERIFY) /dafnyVerify:0 $< && touch $@ && rm -f $(dir $@)inprogress.$(notdir $@)

.PRECIOUS: obj/%.o

$(DOTOs): obj/%.o: obj/%.cpp $(DAFNY_RUNTIME_DIR)/DafnyRuntime.h
	@echo $(BOLD)"[+] Compiling $*"$(RESET)
	@$(CXX) $(CXXFLAGS) -I. -c -o $@ $<

.PRECIOUS: obj/%.cpp

obj/%.cpp: %.dfy $(DAFNY_DEPS) | obj
	@echo $(BOLD)"[+] Extracting $*"$(RESET)
	@ \
	TEMPFILE=$$(mktemp); \
	$(DAFNY) \
		/nologo /noVerify /compile:0 \
		/printVerifiedProceduresCount:0 \
		/spillTargetCode:3 /compileTarget:cpp \
		$(DOTHs) $< 2>&1 \
	| grep -v 'Dafny program verifier finished' \
	| grep -v 'Compiled program written to' \
	| sed '/^[[:space:]]*$$/d' \
	| awk 'tolower($$0)~/error|fatal/{$$0=$(BOLD) $$0}{print $(RED) $$0 $(RESET)}' \
	| tee $$TEMPFILE; \
	if [ -s $$TEMPFILE ]; then rm $$TEMPFILE; touch $<; exit 1; else rm $$TEMPFILE; fi
	@mv $(notdir $@) $@
	@clang-format -i $@

csharps: $(CSs)
.PRECIOUS: obj/%.cs
obj/%.cs: %.dfy $(DAFNY_DEPS) | obj
	@echo $(BOLD)"[+] Extracting $@"$(RESET)
	@ \
	TEMPFILE=$$(mktemp); \
	$(DAFNY) \
		/nologo /noVerify /compile:0 \
		/printVerifiedProceduresCount:0 \
		/spillTargetCode:3 /compileTarget:cs \
		$< \
	| grep -v 'Dafny program verifier finished' \
	| grep -v 'Compiled program written to' \
	| sed '/^[[:space:]]*$$/d' \
	| awk 'tolower($$0)~/error|fatal/{$$0=$(BOLD) $$0}{print $(RED) $$0 $(RESET)}' \
	| tee $$TEMPFILE; \
	if [ -s $$TEMPFILE ]; then rm $$TEMPFILE; touch $<; exit 1; else rm $$TEMPFILE; fi


initialize:
	@cp .git/hooks/pre-commit.sample .git/hooks/pre-commit 2>/dev/null && \
		echo $(BOLD)"[+] Set up pre-commit hook"$(RESET) || \
		echo $(BRIGHTRED)"[!!!] "$(RESET)$(BOLD)"Cannot find .git/hooks/pre-commit.sample"$(RESET)

syntax-check:
	@$(MAKE) DAFNY_SYNTAX_CHECK=1 -j -k verify

.depend: $(DFYs) Makefile
	@echo '' > $@
	@echo 'IGNORE_DEPENDENCY_GRAPH?=' >> $@
	@echo 'ifeq ($$(IGNORE_DEPENDENCY_GRAPH),)' >> $@
	@for i in $(DFYs); do awk '/^include \".*dfy\"$$/{gsub("\"","",$$2); print "obj/'$$i'.ver: obj/" $$2 ".ver\n"}' $$i; done >> $@
	@for i in $(DFYs); do awk '/^include \".*dfy\"$$/{gsub("\"","",$$2); print "obj/'$$i'.versyn: obj/" $$2 ".versyn\n"}' $$i; done >> $@
	@for i in $(DFYs); do awk '/^include \".*dfy\"$$/{gsub("\"","",$$2); print "obj/'$$i': obj/" $$2 "\n"}' $$i; done | sed 's/\.dfy/\.cpp/g' >> $@
	@for i in $(DFYs); do awk '/^include \".*dfy\"$$/{gsub("\"","",$$2); print "obj/'$$i': obj/" $$2 "\n"}' $$i; done | sed 's/\.dfy/\.o/g' >> $@
	@for i in $(DFYs); do awk '/^include \".*dfy\"$$/{gsub("\"","",$$2); print "obj/'$$i': obj/" $$2 "\n"}' $$i; done | sed 's/\.dfy/\.cs/g' >> $@
	@echo 'endif' >> $@

-include .depend

# Convenience function. Run [make proc-asd] to automatically find the
# correct file that has the "asd" proc in it, and then verify it.
proc-%:
	@for i in $(shell grep -e "\(method\|function\|lemma\|predicate\).*$*" -l $(DFYs)); do \
		echo $(BOLD)"[+] Verifying $* within $$i"$(RESET); \
		time -p $(DAFNY_VERIFY) /proc:*$(subst _,__,$*) $$i | grep -v anon; \
	done

.PHONY: obj/dep.graph obj/dep.png

COMMA:=,
VERIFIED:=$(filter-out inprogress.%,$(patsubst obj/%.dfy.ver,%,$(wildcard obj/*.dfy.ver)))
INPROGRESS:=$(patsubst obj/inprogress.%.dfy.ver,%,$(wildcard obj/inprogress.*.dfy.ver))
COMPILED:=$(patsubst obj/%.o,%,$(wildcard obj/*.o))
EXTRACTED:=$(filter-out $(COMPILED), $(patsubst obj/%.cpp,%,$(wildcard obj/*.cpp)))
NOTYETEXTRACTED:=$(filter-out $(EXTRACTED) $(COMPILED), $(patsubst %.dfy,%,$(wildcard *.dfy)))
COLORCOMMAND:=$(foreach V,$(patsubst %.dfy,%,$(wildcard *.dfy)),\
sed '$$i "$(V)" [style="$(if $(filter $(V), $(VERIFIED) $(INPROGRESS)),filled$(COMMA))$(if $(filter $(V), $(COMPILED)),solid)$(if $(filter $(V), $(EXTRACTED)),dashed)$(if $(filter $(V), $(NOTYETEXTRACTED)),dotted)"$(if $(filter $(V), $(VERIFIED) $(INPROGRESS)), $(COMMA) fillcolor=)$(if $(filter $(V), $(INPROGRESS)),"cyan1",$(if $(filter $(V), $(VERIFIED)),"darkolivegreen1"))]' |)

obj/dep.graph: .depend | obj
	@grep '\.ver' .depend | sed 's|obj/||g' | sed 's/\.dfy\.versyn//g' | sed 's/\.dfy\.ver//g' | sed 's/\.//g' | sed 's/:/ ->/g' | awk 'BEGIN{print "digraph {"}{print "    \"" $$1 "\" " $$2 " \"" $$3 "\"" ""}END{print "}"}' > $@
	@echo $(BOLD)"[+] Generated dep.graph"$(RESET)

dep.png: obj/dep.png
	@if command -v eog >/dev/null; then \
		echo $(BOLD)"[+] Opening the file for you :)"$(RESET); \
		eog $<; \
	else \
		echo $(BOLD)"[!] Please find dep.png inside obj/"$(RESET); \
	fi

obj/dep.png: obj/dep.graph | obj
	@tred $< | $(COLORCOMMAND) dot -Tpng -o$@
	@echo $(BOLD)"[+] Generated dep.png"$(RESET)

ready-for-merge:
	@$(MAKE) clean
	@$(MAKE) -j -k verify extract compile || true
	@$(MAKE) obj/dep.png
	@echo "Please check and add dep.png to the PR when merging."

obj/quicdafny.a: $(DOTOs) | obj
	@echo $(BOLD)"[+] Generating archive quicdafny.a"$(RESET)
	@ar rcs $@ $^

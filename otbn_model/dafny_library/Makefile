# Useful targets:
#
# - make
#    Runs verification
# - make verify
#    Runs only verification
# - make ver-%
#    Verify specific file
# - make proc-%
#    Verify a single procedure
# - make initialize
#    Set up githooks properly for this repo to help keep things clean
# - make whitespace-cleanup
#    Clean up whitespace in all of the files in this repo
#
# Useful parameters
#
# - DAFNY: Path to dafny executable
# - DAFNY_ADDITIONAL_ARGS: Additional arguments to pass to dafny. Use 
#     /noNLarith for NL files.
# - TIMELIMIT: Set a different default timelimit (default: 30s)
# - PROFILE: Turn on SMT profiling during verification

DAFNY?=dafny
DAFNY_ADDITIONAL_ARGS?=
DAFNY_DIR?=$(patsubst %/Binaries/,%,$(dir $(realpath $(shell which $(DAFNY)))))
DAFNY_SYNTAX_CHECK?=

TIMELIMIT?=

DAFNY_VERIFY := $(DAFNY) \
	/compile:0 \
	$(DAFNY_ADDITIONAL_ARGS)

ifneq ($(TIMELIMIT),)
  DAFNY_VERIFY += /timeLimit:$(TIMELIMIT)
endif

ifdef PROFILE
DAFNY_VERIFY += "/z3opt:smt.qi.profile=true" "/z3opt:smt.qi.profile_freq=100"
endif

DFYs:=$(wildcard *.dfy) $(wildcard **/*.dfy)

DAFNY_RUNTIME_DIR:=$(DAFNY_DIR)/Binaries

DAFNY_DEPS:= \
	$(DAFNY_RUNTIME_DIR)/Dafny.exe \
	$(DAFNY_RUNTIME_DIR)/DafnyPipeline.dll \
	$(DAFNY_RUNTIME_DIR)/DafnyRuntime.h

BOLD:="\033[1m"
RED:="\033[31m"
BRIGHTRED:="\033[1;31m"
RESET:="\033[0m"

all: verify

verify: $(patsubst %, %-verify, $(DFYs))

%-verify:
	@echo $(BOLD)"[+] Verifying $*"$(RESET)
	@$(DAFNY_VERIFY) $*

whitespace-cleanup:
	@echo $(BOLD)"[+] Cleaning up whitespace for all dafny files"$(RESET)
	@sed -i '' -e "s/[[:blank:]]*$$//" $(DFYs)

initialize:
	@cp .git/hooks/pre-commit.sample .git/hooks/pre-commit 2>/dev/null && \
		echo $(BOLD)"[+] Set up pre-commit hook"$(RESET) || \
		echo $(BRIGHTRED)"[!!!] "$(RESET)$(BOLD)"Cannot find .git/hooks/pre-commit.sample"$(RESET)

# Convenience function. Run [make ver-Sets.dfy] to automatically find all
# files named "Sets.dfy", and then verify them.
ver-%:
	@for i in $(shell find . -name $*); do \
		echo $(BOLD)"[+] Verifying $$i"$(RESET); \
		time -p $(DAFNY_VERIFY) $$i; \
	done


# Convenience function. Run [make proc-asd] to automatically find the
# correct file that has the "asd" proc in it, and then verify it.
proc-%:
	@for i in $(shell grep -e "\(method\|function\|lemma\|predicate\).*$*" -l $(DFYs)); do \
		echo $(BOLD)"[+] Verifying $* within $$i"$(RESET); \
		time -p $(DAFNY_VERIFY) /proc:*$(subst _,__,$*) $$i | grep -v anon; \
	done

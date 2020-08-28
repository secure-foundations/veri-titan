DAFNY_VERIFY := dafny \
	/compile:0 \
	/allocated:3 \
	/nologo \
	/printVerifiedProceduresCount:0 \

VALE=vale.exe

verify:	gen/examples.dfy.ver

gen:
	@echo $(BOLD)"[+] making $@/ directory"$(RESET)
	@mkdir $@

gen/examples.dfy.ver: gen/examples.dfy gen/code_vale.dfy.ver gen/code_example_lemmas.dfy.ver 
	$(DAFNY_VERIFY) $< && touch $@

gen/code_example_lemmas.dfy.ver: code/example_lemmas.dfy
	$(DAFNY_VERIFY) $< && touch $@

gen/code_vale.dfy.ver: code/vale.dfy
	$(DAFNY_VERIFY) $< && touch $@

gen/decls.dfy.ver: gen/decls.dfy
	$(DAFNY_VERIFY) $< && touch $@

gen/examples.dfy: code/examples.vad gen/decls.dfy
	$(VALE) -dafnyText -in $< -out $@

gen/decls.dfy: code/decls.vad
	$(VALE) -dafnyText -in $< -out $@

clean:
	rm -r gen
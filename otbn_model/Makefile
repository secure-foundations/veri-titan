DAFNY_VERIFY := dafny \
	/compile:0 \
	/allocated:3 \
	/nologo \
	/printVerifiedProceduresCount:0 \

verify: code/examples.dfy code/example.s.dfy.ver
	$(DAFNY_VERIFY) code/examples.dfy

code/example.s.dfy.ver: code/example.s.dfy
	$(DAFNY_VERIFY) code/example.s.dfy

code/examples.dfy: code/examples.vad code/decls.dfy
	vale.exe -dafnyText -in code/examples.vad -out code/examples.dfy

code/decls.dfy: code/decls.vad
	vale.exe -dafnyText -in code/decls.vad -out code/decls.dfy

clean:
	rm code/examples.dfy code/decls.dfy
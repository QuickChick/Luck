.PHONY: compile tests clean

compile: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

clean:
         # This might not work on macs, but then not my problem
	find . -regex ".*\.vo\|.*\.d\|.*\.glob\|.*\.o\|.*\.cmi\|.*\.cmx\|.*\.cmxs\|.*\.cmo\|.*\.bak\|.*~" -type f -delete
	rm -f Makefile.coq

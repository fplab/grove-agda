AGDA    ?= agda

.PHONY: all
all : all.agdai

%.agdai : %.agda
	$(AGDA) $*.agda

.PHONY : clean
clean :
	rm -rf _build
	rm -f *.agdai
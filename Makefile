AGDA    ?= agda

.PHONY: all
all : all.agdai

%.agdai : %.agda
	$(AGDA) $*.agda

.PHONY : clean
clean :
	rm -f *.agdai
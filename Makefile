AGDA ?= agda

.PHONY: all
all:
	$(AGDA) Grove.agda

.PHONY : clean
clean :
	rm -rf _build
	rm -f *.agdai

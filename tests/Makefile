.PHONY: all
all: test-fstar test-coq test-lean test-hol4

.PHONY: test-%
test-%:
	cd $* && $(MAKE) all

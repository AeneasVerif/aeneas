.PHONY: all
all: verify-fstar verify-coq verify-lean verify-hol4

.PHONY: verify-%
verify-%:
	cd $* && $(MAKE) all

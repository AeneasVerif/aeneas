CHARON_HOME=../../../charon/charon

all: build test translate

.PHONY: build
build:
	cargo build

.PHONY: test
test:
	cargo test

.PHONY: translate
translate:
	cd $(CHARON_HOME) && cargo run ../../aeneas/examples/misc/src/hashmap.rs

.PHONY: all
all: tests

.PHONY: test
test:
	cargo rustc -- --test -Zpolonius
	cd target/debug/ && ./betree

.PHONY: clean
clean:
	cargo clean

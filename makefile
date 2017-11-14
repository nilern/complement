.PHONY: all
all: compiler vm

.PHONY: compiler
compiler: complotc

.PHONY: vm
vm: vm/target/release/vm

.PHONY: clean
clean: clean-compiler clean-vm

.PHONY: clean-compiler
clean-compiler:
	rm -f complotc

.PHONY: clean-vm
clean-vm:
	cd vm && cargo clean --release -p vm && cd ..

complotc: $(shell find -name "*.rkt")
	raco exe -o complotc main.rkt

vm/target/release/vm: $(shell find vm/src -name "*.rs")
	cd vm && cargo build --release && cd ..

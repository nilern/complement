.PHONY: all
all: $(shell find -name "*.rkt" | sed -r "s/([^\.]*)\.rkt/\/compiled\1_rkt.zo/")

compiled/%_rkt.zo: %.rkt
	raco make $<

.PHONY: clean
clean:
	rm -r compiled

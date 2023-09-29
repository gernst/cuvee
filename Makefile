ALL  = $(wildcard evaluation/lemmas/*.bpl)

BPL = \
	evaluation/lemmas/list/append.bpl \
	evaluation/lemmas/list/filter.bpl \
	evaluation/lemmas/list/length.bpl \
	evaluation/lemmas/list/map.bpl \
	evaluation/lemmas/list/remove.bpl \
	evaluation/lemmas/list/reverse.bpl \
	evaluation/lemmas/list/rotate.bpl \
	evaluation/lemmas/list/runlength.bpl

	# evaluation/lemmas/list/regex.bpl
	# evaluation/lemmas/list/runlength.conditional.bpl
	# evaluation/lemmas/list/runlength_other.bpl
	# evaluation/lemmas/list/take_drop.bpl

SMT2 = $(BPL:%.bpl=%.smt2)
TH   = $(BPL:%.bpl=%.th)

S = $(BPL:%.bpl=%.structural.bpl)
C = $(BPL:%.bpl=%.conditional.bpl)
E = $(BPL:%.bpl=%.enumerate.bpl)
T = $(BPL:%.bpl=%.th.log)

.PHONY: all smt2 th clean

 # don't delete TheSy logs if we interrupt it
.PRECIOUS: %.th.log

structural: $S
conditional: $C
enumerate: $E
thesy: $T

all: $S $C $E $T

th: $(TH)
smt2: $(SMT2)

%.smt2: %.bpl
	./Cuvee.sh $< -o $@ 

%.th: %.bpl
	./Cuvee.sh $< -o $@

%.structural.bpl: %.bpl
	./Cuvee.sh $< -lemmas:structural -o $@

%.conditional.bpl: %.bpl
	./Cuvee.sh $< -lemmas:structural+conditional -o $@

%.enumerate.bpl: %.bpl
	./Cuvee.sh $< -lemmas:enumerate -o $@

%.th.log: %.th
	TheSy $< | tee $@

clean:
	rm -f evaluation/lemmas/*.smt2 evaluation/lemmas/*.th \
	      evaluation/lemmas/*.log evaluation/lemmas/*.stats.json

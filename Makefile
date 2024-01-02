SMALL =\
	evaluation/lemmas/list/append.bpl \
	evaluation/lemmas/list/filter.bpl \
	evaluation/lemmas/list/length.bpl \
	evaluation/lemmas/list/map.bpl \
	evaluation/lemmas/list/remove.bpl \
	evaluation/lemmas/list/reverse.bpl \
	evaluation/lemmas/list/rotate.bpl \
	evaluation/lemmas/list/runlength.bpl

BPL = \
	evaluation/lemmas/list/append.bpl \
	evaluation/lemmas/list/filter.bpl \
	evaluation/lemmas/list/length.bpl \
	evaluation/lemmas/list/map.bpl \
	evaluation/lemmas/list/remove.bpl \
	evaluation/lemmas/list/reverse.bpl \
	evaluation/lemmas/list/rotate.bpl \
	evaluation/lemmas/list/runlength.bpl \
	evaluation/lemmas/nat.bpl \
	evaluation/lemmas/list.bpl \
	evaluation/lemmas/tree.bpl

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

.PHONY: all smt2 th clean compare test

 # don't delete TheSy logs if we interrupt it
.PRECIOUS: %.th.log

structural: $S
conditional: $C
enumerate: $E
thesy: $T

all: $S $C $E $T

TEX = $(BPL:%.bpl=%.tex)
tex: $(TEX)

%.tex: %.bpl %.structural.bpl %.conditional.bpl %.enumerate.bpl %.th.log
	bloop run cuvee -m cuvee.TACAS -- $*
	pandoc $*.md -o $*.html

compare: evaluation/lemmas/structural.txt \
         evaluation/lemmas/conditional.txt \
         evaluation/lemmas/enumerate.txt \
         evaluation/lemmas/thesy.txt

evaluation/lemmas/structural.txt: $(BPL:%.bpl=%.structural.compare.txt)
	cat $^ > $@
evaluation/lemmas/conditional.txt: $(BPL:%.bpl=%.conditional.compare.txt)
	cat $^ > $@
evaluation/lemmas/enumerate.txt: $(BPL:%.bpl=%.enumerate.compare.txt)
	cat $^ > $@
evaluation/lemmas/thesy.txt: $(BPL:%.bpl=%.thesy.compare.txt)
	cat $^ > $@

th: $(TH)
smt2: $(SMT2)

%.smt2: %.bpl
	./Cuvee.sh $< -o $@ 

%.th: %.bpl
	./Cuvee.sh $< -o $@

%.structural.bpl: %.bpl
	time ./Cuvee.sh $< -lemmas:structural -o $@ | tee $*.structural.log

%.conditional.bpl: %.bpl
	time ./Cuvee.sh $< -lemmas:structural+conditional -o $@ | tee $*.conditional.log

%.enumerate.bpl: %.bpl
	./Cuvee.sh $< -lemmas:enumerate -o $@ | tee $*.enumerate.log
	gzip $*.enumerate.log

%.th.log: %.th
	TheSy $< | tee $@

clean:
	rm -f evaluation/lemmas/*.smt2 evaluation/lemmas/*.th \
	      evaluation/lemmas/*.log evaluation/lemmas/*.stats.json

%.structural.compare.txt: %.bpl %.structural.bpl %.conditional.bpl %.enumerate.bpl %.th.log
	./CompareTheories.sh $< $*.structural.bpl $*.conditional.bpl $*.enumerate.bpl $*.th.log > $@

%.conditional.compare.txt: %.bpl %.structural.bpl %.conditional.bpl %.enumerate.bpl %.th.log
	./CompareTheories.sh $< $*.conditional.bpl $*.structural.bpl $*.enumerate.bpl $*.th.log > $@

%.enumerate.compare.txt: %.bpl %.structural.bpl %.conditional.bpl %.enumerate.bpl %.th.log
	./CompareTheories.sh $< $*.enumerate.bpl $*.structural.bpl $*.conditional.bpl $*.th.log > $@

%.thesy.compare.txt: %.bpl %.structural.bpl %.conditional.bpl %.enumerate.bpl %.th.log
	./CompareTheories.sh $< $*.th.log $*.structural.bpl $*.conditional.bpl $*.enumerate.bpl > $@
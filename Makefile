BPL  = $(wildcard evaluation/lemmas/*.bpl)
SMT2 = $(BPL:%.bpl=%.smt2)
TH   = $(BPL:%.bpl=%.th)

.PHONY: smt2 th clean



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
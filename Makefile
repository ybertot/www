
### Coq website : generation of static pages ###

DST:=dest
PP:=yamlpp-0.3/yamlpp
INCLS:=incl/header.html incl/footer.html incl/news/recent.html
DEPS:=$(INCLS) $(PP)

all: pages news conf

aliases: pagesaliases newsaliases

clean:
	rm -rf $(DST)/*
	rm -rf .*.stamp
	rm -f incl/news/recent.html
	rm -f $(PP) $(PP).cm* $(PP).o

## In case we need to regenerate yamlpp.ml from its .mll.

$(PP).ml: $(PP).mll
	ocamllex $<

## If ocamlopt is there, we use it to compile yamlpp, otherwise we use
## the yamlpp.ml as an ocaml script...

$(PP): $(PP).ml
	ocamlopt -o $@ $< || printf 'ocaml %s "$$@"' $< > $@
	chmod +x $@

.PHONY: all pages news conf pagesaliases newsaliases clean

## Generated pages, listed in the PAGESINDEX file

PAGES:= $(shell cut -f1 -d: PAGESINDEX | uniq)
PAGESDST:=$(patsubst %,$(DST)/node/%.html, $(PAGES))

pages: $(PAGESDST)

$(DST)/node/%: pages/% $(DEPS)
	mkdir -p $(dir $@) && $(PP) $< -o $@

## Page aliases through Apache RewriteRule...

conf: $(DST)/aliases.conf

$(DST)/aliases.conf: PAGESINDEX NEWSINDEX
	sed -n -e "s|\(.\+\):\(.\+\)|RewriteRule ^\2$$ /node/\1.html [L]|p" PAGESINDEX > $@
	sed -n -e "s|\(.\+\):\(.\+\)|RewriteRule ^/news/\2$$ /news/\1.html [L]|p" NEWSINDEX >> $@
	sed -n -e "s|\(.\+\):\(.\+\)|RewriteRule ^\2$$ /news/\2 [L,R=301]|p" NEWSINDEX >> $@

## Aliases. Handled here via symbolink links, could also be Apache redirects

pagesaliases: .pagesaliases.stamp \
	$(DST)/styles \
	$(DST)/files \
	$(DST)/coq-workshop/files \
	$(DST)/coq-workshop/2009/cfp/index.html

.pagesaliases.stamp: PAGESINDEX
	IFS=':'; while read a b; \
	do [ -n "$$b" ] && mkdir -p $(DST)/$$b && \
	ln -snf $$PWD/$(DST)/node/$$a.html $(DST)/$$b/index.html; \
	done < PAGESINDEX; touch $@

## Special aliases

$(DST)/files:
	ln -snf ../files $@

$(DST)/styles:
	ln -snf ../styles $@

$(DST)/coq-workshop/files: 
	mkdir -p $(dir $@) && ln -snf ../files $@

$(DST)/coq-workshop/2009/cfp/index.html:
	mkdir -p $(dir $@) && ln -snf $$PWD/$(DST)/news/69.html $@

## News, listed in the NEWSINDEX file

NEWS:= $(shell cut -f1 -d: NEWSINDEX | sort -r -n)

RECENTNEWS:= 128 127 126

NEWSSRC:=$(addprefix news/,$(NEWS))
NEWSDST:=$(patsubst %,$(DST)/news/%.html,$(NEWS))

news: $(DST)/news/index.html $(DST)/rss.xml $(NEWSDST)

incl/news/recent.html: Makefile $(PP) $(addprefix news/,$(RECENTNEWS))
	$(PP) -o $@ $(patsubst %,news/% incl/news/li.html,$(RECENTNEWS))

$(DST)/news/index.html: NEWSINDEX $(NEWSSRC) $(DEPS) incl/news/item.html incl/news/title.html
	mkdir -p $(dir $@)
	$(PP) -o $@ \
          incl/news/title.html \
          incl/header.html \
          $(patsubst %,% incl/news/item.html,$(NEWSSRC)) \
          incl/footer.html

$(DST)/news/%.html: news/% $(DEPS) incl/news/solo.html
	mkdir -p $(dir $@)
	$(PP) $< incl/news/solo.html -o $@

$(DST)/rss.xml: $(NEWSSRC) incl/rss/header.xml incl/rss/footer.xml incl/rss/item.xml $(PP)
	$(PP) -o $@ \
          incl/rss/header.xml \
          $(patsubst %,% incl/rss/item.xml,$(NEWSSRC)) \
          incl/rss/footer.xml

newsaliases: .newsaliases.stamp

.newsaliases.stamp: NEWSINDEX
	IFS=':'; while read a b; \
	do [ -n "$$b" ] && mkdir -p $(DST)/news/$$b && \
	ln -snf ../$$a.html $(DST)/news/$$b/index.html; \
	done < NEWSINDEX; touch $@

printenv:
	@echo "### PAGES ###"
	@echo $(PAGES) | tr " " "\n"
	@echo "### NEWS ###"
	@echo $(NEWS) | tr " " "\n"

# Needs python 2.x (this exists also for python 3, with a different syntax)
run: aliases
	@echo "Starting a local web server for test"
	@echo "It is accessible at: http://localhost:8000"
	cd $(DST) && (python -m http.server 8000 || python -m SimpleHTTPServer 8000)


### Coq website : generation of static pages ###

DST:=dest
YAMLPP:=yamlpp-0.3/yamlpp.ml
INCLS:=incl/header.html incl/footer.html incl/news/recent.html
DEPS:=$(INCLS) $(YAMLPP)

all: pages pagesaliases news newsaliases

clean:
	rm -rf $(DST)/*
	rm -rf .*.stamp

$(YAMLPP): $(YAMLPP:.ml=.mll)
	ocamllex $<

.PHONY: all pages pagesaliases news newsaliases clean

## Generated pages, listed in the PAGES file

PAGES:= $(shell cut -f1 -d: PAGES | uniq)
PAGESDST:=$(patsubst %,$(DST)/node/%.html, $(PAGES))

pages: $(PAGESDST)

$(DST)/node/%: pages/% $(DEPS)
	mkdir -p $(dir $@) && ocaml $(YAMLPP) $< -o $@

## Aliases. Handled here via symbolink links, could also be Apache redirects

pagesaliases: .pagesaliases.stamp \
	$(DST)/styles \
	$(DST)/files \
	$(DST)/coq-workshop/files \
	$(DST)/coq-workshop/2009/cfp/index.html

.pagesaliases.stamp: PAGES
	IFS=':'; while read a b; \
	do [ -n "$$b" ] && mkdir -p $(DST)/$$b && \
	ln -snf $$PWD/$(DST)/node/$$a $(DST)/$$b/index.html; \
	done < PAGES; touch $@

## Special aliases

$(DST)/files:
	ln -snf ../files $@

$(DST)/styles:
	ln -snf ../styles $@

$(DST)/coq-workshop/files: 
	mkdir -p $(dir $@) && ln -snf ../files $@

$(DST)/coq-workshop/2009/cfp/index.html:
	mkdir -p $(dir $@) && ln -snf $$PWD/$(DST)/news/69.html $@

## News, listed in the NEWS file

NEWS:= $(shell cut -f1 -d: NEWS | sort -r -n)

RECENTNEWS:= 122

NEWSSRC:=$(addprefix news/,$(NEWS))
NEWSDST:=$(patsubst %,$(DST)/news/%.html,$(NEWS))

news: $(DST)/news/index.html $(DST)/rss.xml $(NEWSDST)

incl/news/recent.html: $(YAMLPP) $(addprefix news/,$(RECENTNEWS))
	ocaml $(YAMLPP) -o $@ $(patsubst %,news/% incl/news/li.html,$(RECENTNEWS))

$(DST)/news/index.html: $(NEWSSRC) $(DEPS) incl/news/item.html incl/news/title.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) -o $@ \
          incl/news/title.html \
          incl/header.html \
          $(patsubst %,% incl/news/item.html,$(NEWSSRC)) \
          incl/footer.html

$(DST)/news/%.html: news/% $(DEPS) incl/news/solo.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) $< incl/news/solo.html -o $@

$(DST)/rss.xml: $(NEWSSRC) incl/rss/header.xml incl/rss/footer.xml incl/rss/item.xml $(YAMLPP)
	ocaml $(YAMLPP) -o $@ \
          incl/rss/header.xml \
          $(patsubst %,% incl/rss/item.xml,$(NEWSSRC)) \
          incl/rss/footer.xml

newsaliases: .newsaliases.stamp

.newsaliases.stamp: NEWS
	IFS=':'; while read a b; \
	do [ -n "$$b" ] && mkdir -p $(DST)/news/$$b && \
	ln -snf ../$$a.html $(DST)/news/$$b/index.html; \
	done < NEWS; touch $@

printenv:
	@echo "### PAGES ###"
	@echo $(PAGES) | tr " " "\n"
	@echo "### NEWS ###"
	@echo $(NEWS) | tr " " "\n"

# Needs python 2.x (this exists also for python 3, with a different syntax)
run:
	@echo "Starting a local web server for test"
	@echo "It is accessible at: http://localhost:8000"
	cd $(DST) && python -m SimpleHTTPServer 8000


all: jaza

.PHONY: jaza-image
jaza-image: Dockerfile
	docker build -f Dockerfile -t jaza .

.PHONY: jaza-build-image
jaza-build-image: Dockerfile
	docker build -f Dockerfile-build -t jaza-build .

.PHONY: run
run: jaza-image
	docker run -i -t --rm -v $(PWD):/root/jaza/workdir jaza $*

.PHONY: 
jaza: jaza-build-image
	docker run --rm -v $(PWD)/src:/root jaza-build
	docker run --rm -v $(PWD)/src:/root jaza-build cat jaza >jaza
	chmod 755 jaza
	file jaza

.PHONY: clean
clean: 
	rm -f jaza

.PHONY: tidy
tidy: clean
	docker rmi jaza
	docker rmi jaza-build


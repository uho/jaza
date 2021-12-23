
all: jaza

# Create environment to run old i386 Jaza binary
.PHONY: jaza-image
jaza-image: Dockerfile
	docker build -f Dockerfile -t jaza .

# Run Jaza with Hugs
.PHONY: run
run: jaza-image
	docker run -i -t --rm -v $(PWD)/src:/root jaza $*

# Create environemtn to build amd64 Jaza executable
.PHONY: jaza-build-image
jaza-build-image: Dockerfile
	docker build -f Dockerfile-build -t jaza-build .

.PHONY: 
jaza: jaza-build-image
	docker run --rm -v $(PWD)/src:/root jaza-build
	chmod 755 src/jaza
	file src/jaza

.PHONY: clean
clean: 
	rm -f src/jaza
	rm -f src/*.o
	rm -f src/*.hi

.PHONY: tidy
tidy: clean
	docker rmi jaza
	docker rmi jaza-build


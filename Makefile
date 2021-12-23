
all: src/jaza

# Create environment to run old i386 Jaza binary
.PHONY: jaza-image
jaza-image: Dockerfile
	docker build -f Dockerfile -t jaza .

# Run Jaza with Hugs
.PHONY: run
run: jaza-image
	docker run -i -t --rm -v $(PWD)/src:/root jaza $*

# Create environment to build amd64 Jaza executable
.PHONY: jaza-build-image
jaza-build-image: Dockerfile-build lib/libffi.so.7
	docker build -f Dockerfile-build -t jaza-build .

lib:
	mkdir $@

lib/libffi.so.7: lib
	docker run --rm debian:bullseye-slim cat /usr/lib/x86_64-linux-gnu/libffi.so.7 >lib/libffi.so.7

src/jaza: jaza-build-image
	docker run --rm -v $(PWD)/src:/root -e UID=`id -u` -e GID=`id -g` jaza-build
	chmod 755 src/jaza
	ls -al src/jaza
	file src/jaza

.PHONY: clean
clean: 
	rm -f src/jaza
	rm -f src/*.o
	rm -f src/*.hi

.PHONY: tidy
tidy: clean
	rm -rf lib
	docker rmi -f jaza
	docker rmi -f jaza-build


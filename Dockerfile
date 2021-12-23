# Make docker container that can run the Jaza binary
FROM debian:bullseye-slim
RUN dpkg --add-architecture i386

RUN apt update && apt upgrade -y
RUN apt install -y binutils:i386 libreadline8:i386 libncurses5:i386 libgmp3-dev:i386

# fake old libraries
RUN cd /lib/i386-linux-gnu && ln -s libreadline.so.8 libreadline.so.4
RUN cd /usr/lib/i386-linux-gnu && ln -s libgmp.so libgmp.so.3

# extract Jaza from dist
COPY dist/jaza_1_1_linux.tgz .
WORKDIR /root
RUN tar xfz /jaza_1_1_linux.tgz && rm /jaza_1_1_linux.tgz

RUN mkdir /root/jaza/workdir
WORKDIR /root/jaza/workdir

ENTRYPOINT ["/root/jaza/jaza"]

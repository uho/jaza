FROM lpenz/debian-squeeze-amd64

RUN apt-get update && apt-get upgrade -y

# Jaza from source (Hugs)
RUN apt-get install -y --force-yes hugs

VOLUME /root
WORKDIR /root
RUN cp /usr/lib/hugs/oldlib/Pretty.lhs /tmp

CMD ["runhugs", "TextUI"]

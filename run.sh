containerId=pedagand/velus

command -v docker >/dev/null 2>&1 || { \
        echo >&2 "docker is required but could not be found.  Aborting."; \
        echo >&2 "To setup Docker: https://docs.docker.com/engine/getstarted/step_one/"; \
        exit 1; }

xhost +local:`docker inspect --format='{{ .Config.Hostname }}' $containerId`
docker run -it --rm \
      -e DISPLAY=:0 \
      -v /tmp/.X11-unix:/tmp/.X11-unix \
      -v $PWD:/home/developer/velus \
      $containerId $1

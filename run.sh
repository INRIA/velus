containerId=pedagand/velus

xhost +local:`docker inspect --format='{{ .Config.Hostname }}' $containerId`
docker run -it --rm \
      -e DISPLAY=:0 \
      -v /tmp/.X11-unix:/tmp/.X11-unix \
      -v $PWD:/home/developer/velus \
      $containerId $1

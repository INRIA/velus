#!/bin/bash

sudo chown -R developer.developer $HOME/velus
cd $HOME/velus
make clean
make && bash

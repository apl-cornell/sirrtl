#!/bin/bash
args=$(find tutorial-samples/ -name "*.scala" | awk -F'.' '{print $1}' | awk -F'/' '{print $5}')
sbt -v "project genfir" "runMain solutions.FirrtlGenerator $args"

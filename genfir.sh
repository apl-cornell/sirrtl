#!/bin/bash
arg=$1
sbt -v "project genfir" "runMain solutions.FirrtlGenerator $arg"

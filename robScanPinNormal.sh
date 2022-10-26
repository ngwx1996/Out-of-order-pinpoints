#!/bin/bash
# file name: robScanPinNormal.sh

cd /home/wxn6660/CE456
source /project/extra/pin/3.13/enable
pin -t RobScan.so -- ./matmul256

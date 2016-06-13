#!/bin/sh
# Commented Examples give out of MEMORY Answers
# Call this from within the directory of the demo file of the code
# This script is for performance testing
echo "Results for Moderate Performance Test File:"
echo ""
echo "-----------------------------------"
echo "    Valid Given Safety Examples    "
echo "-----------------------------------"
./demo ./Examples/GivenExamples/CSMACD/f3
#./demo ./Examples/GivenExamples/CSMACD/f4
#./demo ./Examples/GivenExamples/CSMACD/f5
./demo ./Examples/GivenExamples/FDDI/f20
./demo ./Examples/GivenExamples/FDDI/in20
./demo ./Examples/GivenExamples/FDDI/f30
./demo ./Examples/GivenExamples/FDDI/in30
./demo ./Examples/GivenExamples/FISCHER/in4
./demo ./Examples/GivenExamples/FISCHER/in5
./demo ./Examples/GivenExamples/FISCHER/in6
#./demo ./Examples/GivenExamples/FISCHER/in7
./demo ./Examples/GivenExamples/LBOUND/ff6
./demo ./Examples/GivenExamples/LBOUND/in4
./demo ./Examples/GivenExamples/LBOUND/in5
#./demo ./Examples/GivenExamples/LBOUND/in6
./demo ./Examples/GivenExamples/LEADER/f5
./demo ./Examples/GivenExamples/LEADER/f6
./demo ./Examples/GivenExamples/LEADER/in5
./demo ./Examples/GivenExamples/LEADER/in6
./demo ./Examples/GivenExamples/LEADER/in7
./demo ./Examples/GivenExamples/PATHOS/in3
#./demo ./Examples/GivenExamples/PATHOS/in4
echo ""
echo "-------------------------------------"
echo "    Invalid Given Safety Examples    "
echo "-------------------------------------"
./demo ./Examples/GivenExamples/FISCHER/in20.e
./demo ./Examples/GivenExamples/FISCHER/in20.f
#./demo ./Examples/GivenExamples/FISCHER/in30.e
#./demo ./Examples/GivenExamples/FISCHER/in30.f
#./demo ./Examples/GivenExamples/FISCHER/in60.e
./demo ./Examples/GivenExamples/PATHOS/f4
#./demo ./Examples/GivenExamples/PATHOS/f6
echo ""
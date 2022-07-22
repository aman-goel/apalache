#!/usr/bin/env bash

./scripts/run_retla.sh test/TwoPhaseUFO.tla "--inv=TCConsistent"
./scripts/run_retla.sh test/TCommitUFO.tla "--inv=TCConsistent"
./scripts/run_retla.sh test/lockserverUFO.tla "--inv=Inv"
./scripts/run_retla.sh test/simple_decentralized_lockUFO.tla "--inv=Inv"
./scripts/run_retla.sh test/sharded_kvUFO.tla "--inv=Safety"

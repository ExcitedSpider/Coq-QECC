#!/usr/bin/env zx
import path from 'path';

$.verbose = true;

await cd(path.join(__dirname, "../theories"));

console.log('Start Dune')

process.env.DUNE_BUILD_WARNINGS = 'false'
await $`dune build --watch --display=quiet`

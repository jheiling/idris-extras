#!/bin/bash

idris --build extras.ipkg &&
idris --mkdoc extras.ipkg

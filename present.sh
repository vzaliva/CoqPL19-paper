#!/bin/sh

# disable desktop notifications
# (for `dunst` daemon on Lunux)
notify-send DUNST_COMMAND_PAUSE

pympress slides-horizontal.pdf
#pdfpc -s -w -c --notes=bottom proposal-slides.pdf

# re-enable desktop notifications
notify-send DUNST_COMMAND_RESUME


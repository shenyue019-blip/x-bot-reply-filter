# X Bot Reply Filter

Tampermonkey userscript for filtering and queue-blocking likely bot or spam replies on X.

## Install

Quick one-click block button for X comments:

https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-quick-block.user.js

Full bot reply filter:

Open this URL in Tampermonkey:

https://raw.githubusercontent.com/shenyue019-blip/x-bot-reply-filter/main/x-bot-reply-filter.user.js

## Notes

- Filtering and logs run locally in the browser.
- The quick block script adds a small `禁` button to reply tweets, hides the clicked reply immediately, blocks the first queued user immediately, waits 15 seconds between later blocks, pauses 30 seconds every 20 blocks, pauses 5 minutes every 60 blocks, and shows draggable/resizable pending/blocking and blocked queues with avatar, username, emoji-safe comment text, and undo controls.
- Auto block uses the current X web login session and runs through the review queue with configurable delays.
- False positive cards can whitelist a user and attempt to unblock them.

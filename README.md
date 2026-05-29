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
- The quick block script adds a small `禁` button to reply tweets, hides the clicked reply immediately, keeps at least 3 minutes between successful blocks, rate-limits blocking to no more than 10 per rolling 30 minutes, 20 per rolling hour, and 100 per rolling 24 hours, shows detailed failure reasons, auto-retries transient failures, removes not-found users from the queue, and includes one-click retry for all failed items.
- Auto block uses the current X web login session and runs through the review queue with configurable delays.
- False positive cards can whitelist a user and attempt to unblock them.

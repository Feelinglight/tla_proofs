---- MODULE MC ----
EXTENDS eeprom_safe_map, TLC

PagesCount_ == 3
PageSize_ == 3
MAX_KEYS_COUNT_ == 2
startKeyValue == 8
ALLOWED_KEYS_ == (1 + startKeyValue)..(startKeyValue + MAX_KEYS_COUNT_ + 1)

DATA_SECTORS_COUNT_ ==
  IF MAX_KEYS_COUNT % PageSize = 0
  THEN MAX_KEYS_COUNT \div PageSize
  ELSE (MAX_KEYS_COUNT \div PageSize) + 1

====

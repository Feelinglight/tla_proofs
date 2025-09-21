---- MODULE MC ----
EXTENDS eeprom_safe_map, TLC

PagesCount_ == 3
PageSize_ == 3
MAX_KEYS_COUNT_ == 3

DATA_SECTORS_COUNT_ ==
  IF MAX_KEYS_COUNT % PageSize = 0
  THEN MAX_KEYS_COUNT \div PageSize
  ELSE (MAX_KEYS_COUNT \div PageSize) + 1

====

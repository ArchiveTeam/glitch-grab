local urlparse = require("socket.url")
local http = require("socket.http")
local https = require("ssl.https")
local cjson = require("cjson")
local utf8 = require("utf8")
local html_entities = require("htmlEntities")
local lfs = require("lfs")

local item_dir = os.getenv("item_dir")
local warc_file_base = os.getenv("warc_file_base")
local concurrency = tonumber(os.getenv("concurrency"))
local item_type = nil
local item_name = nil
local item_value = nil
local item_user = nil

local url_count = 0
local tries = 0
local downloaded = {}
local seen_200 = {}
local addedtolist = {}
local abortgrab = false
local killgrab = false
local logged_response = false

local discovered_outlinks = {}
local discovered_items = {}
local bad_items = {}
local ids = {}

local retry_url = false
local is_initial_url = true

abort_item = function(item)
  abortgrab = true
  --killgrab = true
  if not item then
    item = item_name
  end
  if not bad_items[item] then
    io.stdout:write("Aborting item " .. item .. ".\n")
    io.stdout:flush()
    bad_items[item] = true
  end
end

kill_grab = function(item)
  io.stdout:write("Aborting crawling.\n")
  killgrab = true
end

read_file = function(file)
  if file then
    local f = assert(io.open(file))
    local data = f:read("*all")
    f:close()
    return data
  else
    return ""
  end
end

processed = function(url)
  if downloaded[url] or addedtolist[url] then
    return true
  end
  return false
end

discover_item = function(target, item)
  if not target[item] then
--print("discovered", item)
    target[item] = true
    return true
  end
  return false
end

find_item = function(url)
  if ids[url] then
    return nil
  end
  local value = nil
  local type_ = nil
  for pattern, name in pairs({
    ["^https?://api%.glitch%.com/v1/projects/by/domain%?domain=([^%?&;]+)$"]="domain",
    ["^https?://(cdn%.glitch%..+)$"]="asset",
    ["^https?://(cdn%.hyperdev%.com.+)$"]="asset",
    ["^https?://(cdn%.gomix%.com.+)$"]="asset",
  }) do
    value = string.match(url, pattern)
    type_ = name
    if value then
      break
    end
  end
  if value and type_ then
    return {
      ["value"]=value,
      ["type"]=type_
    }
  end
end

set_item = function(url)
  found = find_item(url)
  if found then
    local newcontext = {}
    new_item_type = found["type"]
    new_item_value = found["value"]
    new_item_name = new_item_type .. ":" .. new_item_value
    local post_id = string.match(new_item_value, ":([^:]+)$")
    if new_item_name ~= item_name then
      ids = {}
      context = newcontext
      item_value = new_item_value
      item_type = new_item_type
      ids[string.lower(item_value)] = true
      abortgrab = false
      tries = 0
      retry_url = false
      is_initial_url = true
      item_name = new_item_name
      print("Archiving item " .. item_name)
    end
  end
end

percent_encode_url = function(url)
  temp = ""
  for c in string.gmatch(url, "(.)") do
    local b = string.byte(c)
    if b < 32 or b > 126 then
      c = string.format("%%%02X", b)
    end
    temp = temp .. c
  end
  return temp
end

allowed = function(url, parenturl)
  local noscheme = string.match(url, "^https?://(.*)$")

  if ids[url]
    or (noscheme and ids[string.lower(noscheme)]) then
    return true
  end

  if string.match(url, "^https?://[^/]+/__") then
    return false
  end

  local skip = false
  for pattern, type_ in pairs({
    ["^https?://(cdn%.glitch%..+)$"]="asset",
    ["^https?://(cdn%.hyperdev%.com.+)$"]="asset",
    ["^https?://(cdn%.gomix%.com.+)$"]="asset",
    ["^https?://([^%.]+%.glitch%.me/.*)$"]="glitchme",
    ["^https?://api%.glitch%.com/git/([^/]+)"]="git"
  }) do
    match = string.match(url, pattern)
    if match
      and (
        type_ ~= "glitchme"
        or not string.match(match, "^cdn%.")
      ) then
      local new_item = type_ .. ":" .. match
      if new_item ~= item_name then
        discover_item(discovered_items, new_item)
        skip = true
      end
    end
  end
  if skip then
    return false
  end

  if not string.match(url, "^https?://[^/]*glitch%.com/")
    and not string.match(url, "^https?://[^/]*glitch%.me/")
    and not string.match(url, "^https?://[^/]*glitch%.global/") then
    discover_item(discovered_outlinks, string.match(percent_encode_url(url), "^([^%s]+)"))
    return false
  end

  for _, pattern in pairs({
    "([^%?&;%.]+)",
    "([0-9a-zA-Z_%-]+)",
    "([a-f0-9]+)"
  }) do
    for s in string.gmatch(url, pattern) do
      if ids[string.lower(s)] then
        return true
      end
    end
  end

  return false
end

wget.callbacks.download_child_p = function(urlpos, parent, depth, start_url_parsed, iri, verdict, reason)
  local url = urlpos["url"]["url"]
  local html = urlpos["link_expect_html"]

  if allowed(url, parent["url"])
    and not processed(url) then
    addedtolist[url] = true
    return true
  end

  return false
end

decode_codepoint = function(newurl)
  newurl = string.gsub(
    newurl, "\\[uU]([0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])",
    function (s)
      return utf8.char(tonumber(s, 16))
    end
  )
  return newurl
end

percent_encode_url = function(newurl)
  result = string.gsub(
    newurl, "(.)",
    function (s)
      local b = string.byte(s)
      if b < 32 or b > 126 then
        return string.format("%%%02X", b)
      end
      return s
    end
  )
  return result
end

wget.callbacks.get_urls = function(file, url, is_css, iri)
  local urls = {}
  local html = nil
  local json = nil
  local post_body = nil

  downloaded[url] = true

  if abortgrab then
    return {}
  end

  local function fix_case(newurl)
    if not newurl then
      newurl = ""
    end
    if not string.match(newurl, "^https?://[^/]") then
      return newurl
    end
    if string.match(newurl, "^https?://[^/]+$") then
      newurl = newurl .. "/"
    end
    local a, b = string.match(newurl, "^(https?://[^/]+/)(.*)$")
    return string.lower(a) .. b
  end

  local function check(newurl)
    if not string.match(newurl, "^https?://") then
      return nil
    end
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    newurl = fix_case(newurl)
    local origurl = url
    if string.len(url) == 0
      or string.len(newurl) == 0 then
      return nil
    end
    local url = string.match(newurl, "^([^#]+)")
    local url_ = string.match(url, "^(.-)[%.\\]*$")
    while string.find(url_, "&amp;") do
      url_ = string.gsub(url_, "&amp;", "&")
    end
    if not processed(url_)
      and not processed(url_ .. "/")
      and allowed(url_, origurl) then
      local headers = {}
      if string.match(url_, "^https?://api%.glitch%.com/git/") then
        headers["User-Agent"] = "git/2.30.2"
        headers["Git-Protocol"] = "version=2"
        if post_body then
          headers["Content-Type"] = "application/x-git-upload-pack-request"
          headers["Accept"] = "application/x-git-upload-pack-result"
        end
      end
      if string.match(url_, "^https?://([^%.]+)%.") == item_value then
        headers["Referer"] = string.match(url_, "^(https?://[^/]+)") .. "/"
        if string.match(url_, "^https?://[^/]+/$") then
          headers["Accept"] = "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/png,image/svg+xml,*/*;q=0.8"
        else
          headers["Accept"] = "*/*"
        end
      end
      if not post_body then
        table.insert(urls, {
          url=url_,
          headers=headers
        })
      else
        table.insert(urls, {
          url=url_,
          headers=headers,
          body_data=post_body,
          method="POST"
        })
      end
      addedtolist[url_] = true
      addedtolist[url] = true
    end
  end

  local function checknewurl(newurl)
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "['\"><]") then
      return nil
    end
    if string.match(newurl, "^https?:////") then
      check(string.gsub(newurl, ":////", "://"))
    elseif string.match(newurl, "^https?://") then
      check(newurl)
    elseif string.match(newurl, "^https?:\\/\\?/") then
      check(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^\\/\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^//") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^/") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^%.%./") then
      if string.match(url, "^https?://[^/]+/[^/]+/") then
        check(urlparse.absolute(url, newurl))
      else
        checknewurl(string.match(newurl, "^%.%.(/.+)$"))
      end
    elseif string.match(newurl, "^%./") then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function checknewshorturl(newurl)
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "^%?") then
      check(urlparse.absolute(url, newurl))
    elseif not (
      string.match(newurl, "^https?:\\?/\\?//?/?")
      or string.match(newurl, "^[/\\]")
      or string.match(newurl, "^%./")
      or string.match(newurl, "^[jJ]ava[sS]cript:")
      or string.match(newurl, "^[mM]ail[tT]o:")
      or string.match(newurl, "^vine:")
      or string.match(newurl, "^android%-app:")
      or string.match(newurl, "^ios%-app:")
      or string.match(newurl, "^data:")
      or string.match(newurl, "^irc:")
      or string.match(newurl, "^%${")
    ) then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function set_new_params(newurl, data)
    for param, value in pairs(data) do
      if value == nil then
        value = ""
      elseif type(value) == "string" then
        value = "=" .. value
      end
      if string.match(newurl, "[%?&]" .. param .. "[=&]") then
        newurl = string.gsub(newurl, "([%?&]" .. param .. ")=?[^%?&;]*", "%1" .. value)
      else
        if string.match(newurl, "%?") then
          newurl = newurl .. "&"
        else
          newurl = newurl .. "?"
        end
        newurl = newurl .. param .. value
      end
    end
    return newurl
  end

  local function increment_param(newurl, param, default, step)
    local value = string.match(newurl, "[%?&]" .. param .. "=([0-9]+)")
    if value then
      value = tonumber(value)
      value = value + step
      return set_new_params(newurl, {[param]=tostring(value)})
    else
      if default ~= nil then
        default = tostring(default)
      end
      return set_new_params(newurl, {[param]=default})
    end
  end

  local function get_count(data)
    local count = 0
    for _ in pairs(data) do
      count = count + 1
    end 
    return count
  end

  local function list_tree(d)
    local result = {}
    for name in lfs.dir(d) do
      if name ~= "." and name ~= ".." then
        path = d .. "/" .. name
        if lfs.attributes(path).mode == "directory" then
          for k, v in pairs(list_tree(path)) do
            result[k] = v
          end
        else
          result[path] = true
        end
      end
    end
    return result
  end

  if item_type == "asset" then
    local newurl = string.match(url, "^([^%?]+)")
    check(newurl)
    if string.match(url, "%?") then
      local params = string.match(url, "%?(.+)$")
      if string.match(params, "^v=") then
        check(newurl .. "?" .. string.match(params, "v=(.+)$"))
      else
        check(newurl .. "?v=" .. params)
      end
    end
    if string.match(url, "%?.+Z$") then
      local y, m, d, H, M, S, e = string.match(url, "%?v?=?([0-9][0-9][0-9][0-9])%-([0-9][0-9])%-([0-9][0-9])T([0-9][0-9]):([0-9][0-9]):([0-9][0-9])%.([0-9]+)Z$")
      check(newurl .. "?v=" .. tostring(os.time({day=d,month=m,year=y,hour=H,min=M,sec=S})) .. e)
    elseif string.match(url, "%?[0-9]+$") then
      local timestamp, e = string.match(url, "%?([0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9])([0-9]*)$")
      check(newurl .. "?v=" .. os.date("%Y-%m-%dT%H:%M:%S", tonumber(timestamp)) .. "." .. e .. "Z")
    end
  end

  if allowed(url)
    and status_code < 300
    and item_type ~= "asset" then
    html = read_file(file)
    if string.match(url, "https?://api%.glitch%.com/v1/projects/by/domain%?domain=") then
      local json = cjson.decode(html)
      if not json[item_value] then
        return urls
      end
      check("https://api.glitch.com/v1/projects/by/domain/users?domain=" .. item_value .. "&limit=100")
      check("https://api.glitch.com/v1/projects/by/domain/teams?domain=" .. item_value .. "&limit=100")
      check("https://" .. item_value .. ".glitch.me/")
      check("https://api.glitch.com/projects/" .. item_value .. "?showDeleted=false")
      check("https://api.glitch.com/projects/" .. item_value)
      check("https://api.glitch.com/git/" .. item_value .. "/info/refs?service=git-upload-pack")
      check("https://glitch.com/~" .. item_value)
      local id = json[item_value]["id"]
      ids[id] = true
      check("https://api.glitch.com/v1/projects/by/id/collections?id=" .. id .. "&limit=100")
      check("https://api.glitch.com/v1/projects/by/id/teams?id=" .. id .. "&limit=100")
      check("https://api.glitch.com/v1/projects/by/id/users?id=" .. id .. "&limit=100")
      check("https://api.glitch.com/v1/projects/by/id?id=" .. id)
    end
    if string.match(url, "^https?://[^/]+/~") then
      local found = false
      for s in string.gmatch(html, "/project%-avatar/([0-9a-f%-]+)") do
        if ids[s] then
          found = true
          break
        end
      end
      if not found then
        error("Web page may be loaded incomplete.")
      end
    end
    if string.match(url, "/git/[^/]+/info/refs%?service=git%-upload%-pack$") then
      if not string.match(html, "multi_ack thin%-pack side%-band side%-band%-64k ofs%-delta shallow no%-progress include%-tag multi_ack_detailed no%-done") then
        error("Expected different git server response.")
      end
      local hash = string.match(html, "000000[0-9a-f][0-9a-f]([0-9a-f]+) HEAD")
      if not hash then
        error("Could not find hash.")
      end
      if string.len(hash) ~= 40 then
        error("Found incorrect hash length.")
      end
      context["hash"] = hash
      post_body = 
        "0080want " .. hash .. " multi_ack_detailed no-done side-band-64k thin-pack ofs-delta agent=git/2.30.2\n"
        .. "0000"
        .. "0009done\n"
      checknewurl("/git/" .. item_value .. "/git-upload-pack")
    end
    if string.match(url, "/git/[^/]+/git%-upload%-pack$") then
      local temp = html
      local found_nak = false
      local header = nil
      local data = nil
      local channel = nil
      local pack = ""
      local function read_n(s, n)
        local a = string.sub(s, 1, n)
        local b = string.sub(s, n+1)
        return a, b
      end
      while true do
        header = nil
        data = nil
        channel = nil
        header, temp = read_n(temp, 4)
        if not header or #header ~= 4 then
          break
        end
        header = tonumber(header, 16)
        if header ~= 0 then
          data, temp = read_n(temp, header-4)
          if not found_nak then
            if data ~= "NAK\n" then
              error("Found incorrect first line value \"" .. data .. "\".")
            end
            found_nak = true
          else
            if not data or #data < header - 4 then
              error("Could not extract data.")
            end
            channel, data = read_n(data, 1)
            channel = string.byte(channel)
            if channel == 1 then
              pack = pack .. data
            elseif channel == 2 then
              -- informational
            elseif channel == 3 then
              error("Got error \"" .. data .. "\".")
            else
              error("Unexpected channel " .. tostring(channel) .. ".")
            end
          end
        end
      end
      if #pack == 0 then
        error("Did not find pack data.")
      end
      local pack_filename = file .. "_git.pack"
      local pack_file = io.open(pack_filename, "wb")
      pack_file:write(pack)
      pack_file:close()
      local repo_dir = item_dir .. "/repo"
      local cd = "cd " .. repo_dir .. " && "
      os.execute("mkdir " .. repo_dir)
      os.execute(cd .. "git init .")
      os.execute("mv " .. pack_filename .. " " .. repo_dir .. "/.git/objects/pack/")
      os.execute(cd .. "git index-pack --stdin < .git/objects/pack/" .. string.match(pack_filename, "([^/]+)$"))
      os.execute(cd .. "git update-ref refs/heads/master " .. context["hash"])
      os.execute(cd .. "git checkout master")
      local num_queued = 0
      for filepath, _ in pairs(list_tree(repo_dir)) do
        filepath = string.sub(filepath, #repo_dir+1)
        if not string.match(filepath, "/%.") then
          check("https://" .. item_value .. ".glitch.me" .. filepath)
          num_queued = num_queued + 1
        end
      end
      --[[if num_queued == 0 then
        error("Nothing was found and queued from the repository...")
      end]]
      local assets_file = io.open(repo_dir .. "/.glitch-assets")
      if assets_file then
        for line in string.gmatch(assets_file:read("*all"), "([^\n]+)") do
          local json = cjson.decode(line)
          if not json["deleted"] then
            check(json["url"])
            check(json["url"] .. "?" .. json["date"])
            local y, m, d, H, M, S, e = string.match(json["date"], "([0-9][0-9][0-9][0-9])%-([0-9][0-9])%-([0-9][0-9])T([0-9][0-9]):([0-9][0-9]):([0-9][0-9])%.([0-9]+)Z")
            while string.len(e) < 3 do
              e = "0" .. e
            end
            check(json["url"] .. "?v=" .. tostring(os.time({day=d,month=m,year=y,hour=H,min=M,sec=S})) .. e)
          end
        end
        assets_file:close()
      end
    end
    local check_f = checknewurl
    if not string.match(html, "<%s*[hH][tT][mM][lL]%[^>]*>") then
      check_f = check
    end
    for newurl in string.gmatch(string.gsub(html, "&[qQ][uU][oO][tT];", '"'), '([^"]+)') do
      if string.match(newurl, "^%.?/")
        and not string.match(newurl, "[%s%*{%(:]") then
        checknewurl(newurl)
      else
        check_f(newurl)
      end
    end
    for newurl in string.gmatch(string.gsub(html, "&#039;", "'"), "([^']+)") do
      if string.match(newurl, "^%.?/")
        and not string.match(newurl, "[%s%*{%(:]") then
        checknewurl(newurl)
      else
        check_f(newurl)
      end
    end
    for newurl in string.gmatch(html, "[^%-]href='([^']+)'") do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, '[^%-]href="([^"]+)"') do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, ":%s*url%(([^%)]+)%)") do
      checknewurl(newurl)
    end
    html = string.gsub(html, "&gt;", ">")
    html = string.gsub(html, "&lt;", "<")
    for newurl in string.gmatch(html, ">%s*([^<%s]+)") do
      check_f(newurl)
    end
  end

  return urls
end

wget.callbacks.write_to_warc = function(url, http_stat)
  status_code = http_stat["statcode"]
  set_item(url["url"])
  url_count = url_count + 1
  io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
  io.stdout:flush()
  logged_response = true
  if not item_name then
    error("No item name found.")
  end
  is_initial_url = false
  if http_stat["statcode"] == 200 then
    local html = read_file(http_stat["local_file"])
    if string.match(html, "<span[^>]+id=\"message\">%s*Waking up%s*</span>") then
      print("Waking up...")
      retry_url = true
      return false
    end
  end
  if http_stat["statcode"] == 403 then
    if string.match(url["url"], "/refs%?service=git%-upload%-pack$") then
      discovered_items["git:" .. item_value] = true
      retry_url = false
      tries = 0
      return false
    elseif string.match(url["url"], "^https?://[^%.]+%.glitch%.me/$") then
      local html = read_file(http_stat["local_file"])
      if string.match(html, "<h1>Oops! This project isn't running%.</h1>")
        and string.match(html, ">Node%.js</a> it relies on is too old%.</p>") then
        retry_url = false
        tries = 0
        return true
      end
    end
  end
  if http_stat["statcode"] ~= 200
    and http_stat["statcode"] ~= 404
    and http_stat["statcode"] ~= 301 then
    print("Bad status code.")
    retry_url = true
    return false
  end
  if http_stat["len"] == 0
    and http_stat["statcode"] < 300 then
    print("Zero byte length.")
    retry_url = true
    return false
  end
  if abortgrab then
    print("Not writing to WARC.")
    return false
  end
  retry_url = false
  tries = 0
  return true
end

wget.callbacks.httploop_result = function(url, err, http_stat)
  status_code = http_stat["statcode"]

  if not logged_response then
    url_count = url_count + 1
    io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
    io.stdout:flush()
  end
  logged_response = false

  if killgrab then
    return wget.actions.ABORT
  end

  set_item(url["url"])
  if not item_name then
    error("No item name found.")
  end

  if abortgrab then
    abort_item()
    return wget.actions.EXIT
  end

  if status_code == 0 or retry_url then
    io.stdout:write("Server returned bad response. ")
    io.stdout:flush()
    tries = tries + 1
    local maxtries = 6
    if tries > maxtries then
      io.stdout:write(" Skipping.\n")
      io.stdout:flush()
      tries = 0
      abort_item()
      return wget.actions.EXIT
    end
    local sleep_time = math.random(
      math.floor(math.pow(2, tries-0.5)),
      math.floor(math.pow(2, tries))
    )
    io.stdout:write("Sleeping " .. sleep_time .. " seconds.\n")
    io.stdout:flush()
    os.execute("sleep " .. sleep_time)
    return wget.actions.CONTINUE
  else
    downloaded[url["url"]] = true
  end

  if status_code >= 300 and status_code <= 399 then
    local newloc = urlparse.absolute(url["url"], http_stat["newloc"])
    if processed(newloc) or not allowed(newloc, url["url"]) then
      tries = 0
      return wget.actions.EXIT
    end
  end

  tries = 0

  return wget.actions.NOTHING
end

wget.callbacks.finish = function(start_time, end_time, wall_time, numurls, total_downloaded_bytes, total_download_time)
  local function submit_backfeed(items, key)
    local tries = 0
    local maxtries = 5
    while tries < maxtries do
      if killgrab then
        return false
      end
      local body, code, headers, status = http.request(
        "https://legacy-api.arpa.li/backfeed/legacy/" .. key,
        items .. "\0"
      )
      if code == 200 and body ~= nil and cjson.decode(body)["status_code"] == 200 then
        io.stdout:write(string.match(body, "^(.-)%s*$") .. "\n")
        io.stdout:flush()
        return nil
      end
      io.stdout:write("Failed to submit discovered URLs." .. tostring(code) .. tostring(body) .. "\n")
      io.stdout:flush()
      os.execute("sleep " .. math.floor(math.pow(2, tries)))
      tries = tries + 1
    end
    kill_grab()
    error()
  end

  local file = io.open(item_dir .. "/" .. warc_file_base .. "_bad-items.txt", "w")
  for url, _ in pairs(bad_items) do
    file:write(url .. "\n")
  end
  file:close()
  for key, data in pairs({
    ["glitch-1ry93h75gz68ovk3"] = discovered_items,
    ["urls-g6ynh7bxs6mnc7gu"] = discovered_outlinks
  }) do
    print("queuing for", string.match(key, "^(.+)%-"))
    local items = nil
    local count = 0
    for item, _ in pairs(data) do
      print("found item", item)
      if items == nil then
        items = item
      else
        items = items .. "\0" .. item
      end
      count = count + 1
      if count == 1000 then
        submit_backfeed(items, key)
        items = nil
        count = 0
      end
    end
    if items ~= nil then
      submit_backfeed(items, key)
    end
  end
end

wget.callbacks.before_exit = function(exit_status, exit_status_string)
  if killgrab then
    return wget.exits.IO_FAIL
  end
  if abortgrab then
    abort_item()
  end
  return exit_status
end



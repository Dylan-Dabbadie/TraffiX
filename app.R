
# ============================================================================
# LIFT — Link-level Interrupted Flow Traffic Dynamics on Spatial Linear
# Networks. An interactive R Shiny research app.
#
# WHAT THIS IMPLEMENTS
#   - Your three supplied equations govern vehicle spacing / event timing:
#       t_event  = max(d_exit, s_entry)      (per-link transition event time)
#       l_eff    = l_veh + g                  (effective vehicle length)
#       V_space  = l_eff / r                  (space-mean / free-flow speed)
#   - Everything else needed to make a runnable simulator (the flow-density
#     relationship, node capacity / merge-diverge logic, and signalised
#     "interruption" behaviour) was NOT specified, so a standard triangular
#     traffic-flow relationships + Cell Transmission Model (Daganzo, 1994/1995)
#     network-loading scheme was used, deliberately built so that:
#       * v_f  (free-flow speed) = l_eff / r        <- your V_space equation
#       * k_jam (jam density)    = 1 / l_eff         <- inverse of l_eff
#       * the CTM "sending" function operationalises the d_exit side and the
#         "receiving" function operationalises the s_entry side of your
#         t_event equation: the flow actually admitted between two cells (or
#         across a node) is the binding (minimum) of the two, which is the
#         flow-conservation counterpart of your max(.,.) event-time rule.
#   All of this is clearly flagged again in the "Model" tab of the app, and
#   the simulation engine lives in one function (simulate_network) so you can
#   swap in your own traffic-flow relationships / capacity rule later without
#   touching the UI.
# ============================================================================

# ---- Packages --------------------------------------------------------------
suppressPackageStartupMessages({
  library(shiny)
  library(shinydashboard)
  library(igraph)
  library(visNetwork)
  library(plotly)
  library(DT)
  library(scales)
  library(leaflet)
  library(jsonlite)
})
# small compatibility shim: older/newer igraph use as.directed()/as_directed()
as_directed_compat <- function(g, mode = "mutual") {
  if (exists("as_directed", mode = "function")) as_directed(g, mode = mode) else as.directed(g, mode = mode)
}

# ============================================================================
# 1. NETWORK CONSTRUCTION
# ============================================================================

#' Build a directed spatial linear network of a given topology.
#' Returns a list with an igraph object, node coordinates, edge lengths (m),
#' and node roles ("source" / "sink" / "junction").
build_network <- function(type = c("corridor", "ring", "grid", "random"),
                           n_nodes = 8, seed = 42) {
  type <- match.arg(type)
  set.seed(seed)

  if (type == "corridor") {
    n <- n_nodes
    g <- make_graph(edges = as.vector(rbind(1:(n - 1), 2:n)), n = n, directed = TRUE)
    coords <- cbind(x = seq_len(n) - 1, y = 0)
    roles <- rep("junction", n); roles[1] <- "source"; roles[n] <- "sink"

  } else if (type == "ring") {
    n <- n_nodes
    g <- make_ring(n, directed = TRUE, mutual = FALSE)
    theta <- seq(0, 2 * pi, length.out = n + 1)[1:n]
    coords <- cbind(x = cos(theta), y = sin(theta))
    roles <- rep("junction", n)
    roles[1] <- "source"
    roles[ceiling(n / 2) + 1] <- "sink"

  } else if (type == "grid") {
    m <- max(2, round(sqrt(n_nodes)))
    g <- make_lattice(dimvector = c(m, m), directed = FALSE)
    g <- as_directed_compat(g, mode = "mutual")
    n <- vcount(g)
    coords <- cbind(x = rep(0:(m - 1), times = m), y = rep(0:(m - 1), each = m))
    roles <- rep("junction", n); roles[1] <- "source"; roles[n] <- "sink"

  } else { # random
    n <- n_nodes
    repeat {
      gu <- sample_gnp(n, p = min(1, 2.2 / n))
      gu <- gu %u% as.undirected(make_tree(n, mode = "undirected")) # guarantee connectivity
      if (is_connected(gu)) break
    }
    g <- as_directed_compat(gu, mode = "mutual")
    lay <- layout_with_fr(g)
    coords <- cbind(x = lay[, 1], y = lay[, 2])
    d <- distances(g, mode = "out")
    src <- 1
    snk <- which.max(d[src, ])
    roles <- rep("junction", n); roles[src] <- "source"; roles[snk] <- "sink"
  }

  colnames(coords) <- c("x", "y")
  V(g)$role <- roles
  V(g)$name <- as.character(seq_len(vcount(g)))

  # edge lengths in metres: base length with mild seeded jitter for realism
  base_len <- switch(type, corridor = 350, ring = 300, grid = 220, random = 260)
  E(g)$length_m <- round(base_len * runif(ecount(g), 0.8, 1.25))

  list(graph = g, coords = coords, roles = roles)
}

#' Project the network's topological (x, y) layout onto a small patch of
#' real map coordinates, so the (otherwise purely topological) LIFT network
#' can be shown as an actual "linear network" on a basemap, the way spatial
#' point data would be. This is a synthetic geo-referencing for display only
#' — the simulation itself has no real-world coordinates. Anchored near
#' Pretoria (Dylan's university) purely as a plausible default study area;
#' change `center_lat` / `center_lon` to relocate it anywhere.
xy_to_latlon <- function(coords, center_lat = -25.7479, center_lon = 28.2293,
                          meters_per_unit = 400) {
  x <- coords[, "x"]; y <- coords[, "y"]
  x <- x - mean(range(x)); y <- y - mean(range(y))
  dx_m <- x * meters_per_unit
  dy_m <- y * meters_per_unit
  dlat <- dy_m / 111320
  dlon <- dx_m / (111320 * cos(center_lat * pi / 180))
  data.frame(lat = center_lat + dlat, lon = center_lon + dlon)
}

# Real-world display corridor used by the interactive Pretoria map.
#
# v17 reliability fix
# -------------------
# The map overlay must NOT change between app launches. Previous builds queried
# Overpass at startup and used an approximate fallback whenever that web request
# timed out. That is why the network sometimes aligned perfectly and sometimes
# appeared off the road.
#
# This version:
#   1. loads a previously verified Lynnwood Road centreline from a persistent
#      local RDS cache whenever one exists;
#   2. if no cache exists, tries several Overpass endpoints;
#   3. validates the returned geometry before accepting it;
#   4. saves the successful geometry locally;
#   5. thereafter reuses exactly the same route on every launch, even offline.
#
# The cache is intentionally outside the temporary Shiny session directory so
# restarting R/RStudio does not remove it.

LYNNWOOD_BBOX <- c(
  south = -25.7700,
  west  =  28.2280,
  north = -25.7525,
  east  =  28.2835
)

TRAFFIX_CACHE_DIR <- file.path(path.expand("~"), ".traffix")
TRAFFIX_ROUTE_CACHE <- file.path(TRAFFIX_CACHE_DIR, "lynnwood_road_centreline_v1.rds")

ensure_traffix_cache_dir <- function() {
  if (!dir.exists(TRAFFIX_CACHE_DIR)) {
    dir.create(TRAFFIX_CACHE_DIR, recursive = TRUE, showWarnings = FALSE)
  }
  invisible(dir.exists(TRAFFIX_CACHE_DIR))
}

validate_lynnwood_centreline <- function(x) {
  is.data.frame(x) &&
    all(c("lat", "lon") %in% names(x)) &&
    nrow(x) >= 25 &&
    all(is.finite(x$lat)) &&
    all(is.finite(x$lon)) &&
    min(x$lon) >= 28.229 &&
    max(x$lon) <= 28.282 &&
    min(x$lat) >= -25.7705 &&
    max(x$lat) <= -25.7520 &&
    diff(range(x$lon)) >= 0.040
}

read_cached_lynnwood_centreline <- function() {
  if (!file.exists(TRAFFIX_ROUTE_CACHE)) return(NULL)

  out <- tryCatch(readRDS(TRAFFIX_ROUTE_CACHE), error = function(e) NULL)
  if (!validate_lynnwood_centreline(out)) return(NULL)

  attr(out, "route_source") <- "cached OpenStreetMap · Lynnwood Road geometry"
  out
}

save_cached_lynnwood_centreline <- function(x) {
  if (!validate_lynnwood_centreline(x)) return(FALSE)
  if (!ensure_traffix_cache_dir()) return(FALSE)

  # Save a clean object; source information is restored on load.
  out <- x[, c("lat", "lon"), drop = FALSE]
  ok <- tryCatch({
    saveRDS(out, TRAFFIX_ROUTE_CACHE)
    TRUE
  }, error = function(e) FALSE)

  ok
}

fetch_lynnwood_osm_centreline <- function() {
  if (!requireNamespace("jsonlite", quietly = TRUE)) {
    stop("Package 'jsonlite' is required for the OSM centreline lookup.")
  }

  bb <- LYNNWOOD_BBOX

  q <- paste0(
    "[out:json][timeout:20];(",
    "way[highway][name='Lynnwood Road'](",
    bb["south"], ",", bb["west"], ",", bb["north"], ",", bb["east"], ");",
    "way[highway][name='Lynnwoodweg'](",
    bb["south"], ",", bb["west"], ",", bb["north"], ",", bb["east"], ");",
    ");out geom;"
  )

  # Trying several public mirrors prevents one temporarily busy Overpass
  # instance from forcing the app onto an approximate fallback.
  overpass_endpoints <- c(
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.nchc.org.tw/api/interpreter"
  )

  old_timeout <- getOption("timeout")
  if (is.null(old_timeout) || !is.finite(old_timeout)) old_timeout <- 60
  on.exit(options(timeout = old_timeout), add = TRUE)
  options(timeout = max(25, old_timeout))

  last_error <- NULL

  for (base in overpass_endpoints) {
    endpoint <- paste0(
      base,
      "?data=",
      utils::URLencode(q, reserved = TRUE)
    )

    obj <- tryCatch(
      jsonlite::fromJSON(endpoint, simplifyVector = FALSE),
      error = function(e) {
        last_error <<- conditionMessage(e)
        NULL
      }
    )

    if (is.null(obj) || is.null(obj$elements) || length(obj$elements) == 0) {
      next
    }

    pts <- do.call(rbind, lapply(obj$elements, function(el) {
      geom <- el$geometry
      if (is.null(geom) || length(geom) < 2) return(NULL)

      do.call(rbind, lapply(geom, function(z) {
        if (is.null(z$lat) || is.null(z$lon)) return(NULL)
        c(lat = as.numeric(z$lat), lon = as.numeric(z$lon))
      }))
    }))

    if (is.null(pts) || nrow(pts) < 20) next

    pts <- as.data.frame(pts)
    pts <- pts[
      is.finite(pts$lat) & is.finite(pts$lon) &
        pts$lon >= 28.2305 & pts$lon <= 28.2805 &
        pts$lat >= -25.7700 & pts$lat <= -25.7530,
      , drop = FALSE
    ]

    if (nrow(pts) < 20) next

    # Lynnwood Road has mapped carriageways in places. Consolidate those into
    # one centreline so simulation nodes do not alternate between lanes.
    bin_width <- 0.00012
    pts$bin <- floor((pts$lon - min(pts$lon)) / bin_width)

    centre <- aggregate(
      cbind(lon, lat) ~ bin,
      data = pts,
      FUN = median,
      na.rm = TRUE
    )

    centre <- centre[order(centre$lon), c("lat", "lon"), drop = FALSE]
    centre <- centre[!duplicated(round(centre$lon, 7)), , drop = FALSE]
    centre <- centre[
      centre$lon >= 28.2310 & centre$lon <= 28.2801,
      , drop = FALSE
    ]

    if (nrow(centre) < 25) next

    # Very light smoothing removes lane-centre jitter without changing bends.
    if (nrow(centre) >= 5) {
      lat_sm <- centre$lat
      lat_sm[2:(nrow(centre) - 1)] <-
        (centre$lat[1:(nrow(centre) - 2)] +
           2 * centre$lat[2:(nrow(centre) - 1)] +
           centre$lat[3:nrow(centre)]) / 4
      centre$lat <- lat_sm
    }

    rownames(centre) <- NULL

    if (validate_lynnwood_centreline(centre)) {
      attr(centre, "route_source") <- "live OpenStreetMap · Lynnwood Road geometry"
      return(centre)
    }
  }

  stop(
    if (is.null(last_error)) {
      "No valid Lynnwood Road geometry was returned by the Overpass mirrors."
    } else {
      paste("Unable to retrieve Lynnwood Road geometry:", last_error)
    }
  )
}

fallback_lynnwood_centreline <- function() {
  # Emergency-only fallback. Once a successful OSM route has been cached this
  # branch should never be used again on the same computer.
  out <- data.frame(
    lat = c(
      -25.75658, -25.75673, -25.75693, -25.75718, -25.75747,
      -25.75778, -25.75810, -25.75843, -25.75876, -25.75908,
      -25.75939, -25.75969, -25.75998, -25.76027, -25.76057,
      -25.76089, -25.76123, -25.76160, -25.76200, -25.76242,
      -25.76285, -25.76329, -25.76374, -25.76418, -25.76460,
      -25.76499, -25.76533, -25.76561, -25.76583, -25.76600,
      -25.76612
    ),
    lon = c(
      28.23104, 28.23255, 28.23405, 28.23560, 28.23715,
      28.23875, 28.24040, 28.24205, 28.24375, 28.24550,
      28.24730, 28.24915, 28.25105, 28.25300, 28.25500,
      28.25705, 28.25915, 28.26130, 28.26350, 28.26575,
      28.26800, 28.27020, 28.27230, 28.27420, 28.27585,
      28.27720, 28.27820, 28.27895, 28.27945, 28.27982,
      28.28008
    )
  )
  attr(out, "route_source") <- "emergency built-in Lynnwood Road fallback"
  out
}

# Route boot sequence ---------------------------------------------------------
# A verified local copy wins. This makes the map deterministic after the first
# successful OSM lookup.
LYNNWOOD_ROUTE <- read_cached_lynnwood_centreline()

if (is.null(LYNNWOOD_ROUTE)) {
  LYNNWOOD_ROUTE <- tryCatch(
    {
      route <- fetch_lynnwood_osm_centreline()
      saved <- save_cached_lynnwood_centreline(route)
      if (saved) {
        attr(route, "route_source") <-
          "OpenStreetMap · Lynnwood Road geometry · cached locally"
      }
      route
    },
    error = function(e) {
      message(
        "TraffiX map: no cached road geometry and OSM lookup failed: ",
        conditionMessage(e)
      )
      fallback_lynnwood_centreline()
    }
  )
}

LYNNWOOD_ROUTE_SOURCE <- attr(LYNNWOOD_ROUTE, "route_source")

# Cumulative local distance along the road geometry.
lynnwood_route_distance <- function() {
  p <- LYNNWOOD_ROUTE
  lat0 <- mean(p$lat)
  dx <- diff(p$lon) * cos(lat0 * pi / 180)
  dy <- diff(p$lat)
  c(0, cumsum(sqrt(dx^2 + dy^2)))
}

# Every simulation node is interpolated ON the master road centreline.
lynnwood_node_positions <- function(n_nodes) {
  stopifnot(n_nodes >= 1)
  p <- LYNNWOOD_ROUTE
  d <- lynnwood_route_distance()

  target <- if (n_nodes == 1) {
    mean(range(d))
  } else {
    seq(min(d), max(d), length.out = n_nodes)
  }

  data.frame(
    lat = approx(d, p$lat, xout = target, ties = "ordered")$y,
    lon = approx(d, p$lon, xout = target, ties = "ordered")$y,
    route_d = target
  )
}

# Every coloured road link uses the corresponding subsection of the SAME
# master centreline. There are no straight chords between nodes.
lynnwood_edge_path <- function(from_node, to_node, n_nodes) {
  p <- LYNNWOOD_ROUTE
  d <- lynnwood_route_distance()
  nodes <- lynnwood_node_positions(n_nodes)

  d1 <- nodes$route_d[from_node]
  d2 <- nodes$route_d[to_node]
  reverse_path <- d2 < d1
  lo <- min(d1, d2)
  hi <- max(d1, d2)

  inner <- which(d > lo & d < hi)
  path_d <- sort(unique(c(lo, d[inner], hi)))

  out <- data.frame(
    lat = approx(d, p$lat, xout = path_d, ties = "ordered")$y,
    lon = approx(d, p$lon, xout = path_d, ties = "ordered")$y
  )

  if (reverse_path) out <- out[nrow(out):1, , drop = FALSE]
  rownames(out) <- NULL
  out
}


# Split one road-link polyline into equal-distance display cells. The simulator
# already uses ncells cells per link; drawing those cells individually lets the
# Lynnwood Road map show a queue front moving THROUGH a link rather than
# reducing the whole link to one average colour.
split_road_path_into_cells <- function(path_df, n_cells) {
  stopifnot(n_cells >= 1, nrow(path_df) >= 2)

  lat0 <- mean(path_df$lat)
  dx <- diff(path_df$lon) * cos(lat0 * pi / 180)
  dy <- diff(path_df$lat)
  d <- c(0, cumsum(sqrt(dx^2 + dy^2)))

  if (!is.finite(max(d)) || max(d) <= 0) {
    return(rep(list(path_df), n_cells))
  }

  bounds <- seq(0, max(d), length.out = n_cells + 1)

  lapply(seq_len(n_cells), function(j) {
    lo <- bounds[j]
    hi <- bounds[j + 1]
    inner <- which(d > lo & d < hi)
    dd <- sort(unique(c(lo, d[inner], hi)))

    data.frame(
      lat = approx(d, path_df$lat, xout = dd, ties = "ordered")$y,
      lon = approx(d, path_df$lon, xout = dd, ties = "ordered")$y
    )
  })
}

# ============================================================================
# 2. FUNDAMENTAL DIAGRAM  (triangular; derived from your equations)
# ============================================================================

#' vf (m/s), kjam (veh/m), w (m/s), qmax (veh/s) from your equations plus a
#' backward-wave-speed factor (the one free parameter your three equations
#' don't pin down).
fd_params <- function(l_veh, g_gap, r, wave_factor) {
  l_eff <- l_veh + g_gap                # your equation 2
  vf    <- l_eff / r                    # your equation 3 (V_space)
  kjam  <- 1 / l_eff                    # inverse spacing at jam
  w     <- wave_factor * vf             # backward (congestion) wave speed
  kc    <- kjam * w / (vf + w)          # critical density (triangular FD)
  qmax  <- vf * kc                      # capacity, veh/s
  list(l_eff = l_eff, vf = vf, kjam = kjam, w = w, kc = kc, qmax = qmax)
}

sending_fn   <- function(k, vf, qmax) pmin(vf * k, qmax)
receiving_fn <- function(k, w, kjam, qmax) pmin(w * (kjam - k), qmax)
speed_fn <- function(k, vf, w, kjam, kc) {
  ifelse(k <= 1e-9, vf, ifelse(k <= kc, vf, pmax(w * (kjam - k) / pmax(k, 1e-9), 0)))
}

# ============================================================================
# 3. NETWORK LOADING SIMULATION  (Cell Transmission Model / Godunov scheme)
# ============================================================================

#' Simulate the network forward in time.
#' t_event = max(d_exit, s_entry) is realised here as: the flow actually
#' transferred between any two adjacent cells (or across a node) is the
#' MIN of what the upstream side can send (its "exit" event, d_exit) and
#' what the downstream side can receive (its "entry" event, s_entry) — the
#' conservation-law dual of a max(.,.) event-time rule: whichever side is
#' the binding constraint sets the transfer.
simulate_network <- function(net, l_veh, g_gap, r, wave_factor,
                              demand_veh_h, cycle_length, green_split,
                              signalize, duration_min, ncells = 4,
                              incident_node = NULL, incident_factor = 1) {
  g <- net$graph
  E_n <- ecount(g); V_n <- vcount(g)
  fd <- fd_params(l_veh, g_gap, r, wave_factor)
  vf <- fd$vf; kjam <- fd$kjam; w <- fd$w; qmax <- fd$qmax

  edge_len <- E(g)$length_m
  dx <- edge_len / ncells
  dt <- max(0.5, min(2, 0.9 * min(dx) / vf))
  duration_s <- duration_min * 60
  nsteps <- ceiling(duration_s / dt)

  demand_rate <- demand_veh_h / 3600 # veh/s

  # incidence lists
  in_edges_of  <- lapply(seq_len(V_n), function(v) as.integer(incident(g, v, mode = "in")))
  out_edges_of <- lapply(seq_len(V_n), function(v) as.integer(incident(g, v, mode = "out")))
  el <- as_edgelist(g, names = FALSE)
  tail_node <- el[, 1]; head_node <- el[, 2]

  role <- V(g)$role
  source_nodes <- which(role == "source")
  sink_nodes   <- which(role == "sink")
  junction_nodes <- which(role == "junction")

  k <- matrix(0.05 * kjam, nrow = E_n, ncol = ncells) # small seed density

  k_hist   <- array(0, dim = c(nsteps + 1, E_n, ncells))
  k_hist[1, , ] <- k
  throughput <- numeric(nsteps + 1)
  cum_out <- 0

  # Store realised link-boundary flows so the application can export the
  # actual simulated inflow/outflow series, not only density snapshots.
  entry_flow_hist <- matrix(0, nrow = nsteps + 1, ncol = E_n)
  exit_flow_hist  <- matrix(0, nrow = nsteps + 1, ncol = E_n)

  for (t in seq_len(nsteps)) {
    time_s <- (t - 1) * dt
    S <- sending_fn(k, vf, qmax)
    R <- receiving_fn(k, w, kjam, qmax)

    # internal cell-to-cell flow within each edge
    flow_internal <- matrix(0, nrow = E_n, ncol = ncells - 1)
    if (ncells > 1) {
      flow_internal <- pmin(S[, 1:(ncells - 1), drop = FALSE], R[, 2:ncells, drop = FALSE])
    }

    entry_flow <- numeric(E_n) # flow entering cell 1 of each edge
    exit_flow  <- numeric(E_n) # flow leaving last cell of each edge

    # --- junction / signal nodes: merge incoming, diverge to outgoing -----
    for (v in junction_nodes) {
      ie <- in_edges_of[[v]]; oe <- out_edges_of[[v]]
      if (length(ie) == 0 || length(oe) == 0) next
      phase_green <- TRUE
      if (isTRUE(signalize)) {
        phase_green <- (time_s %% cycle_length) < (green_split * cycle_length)
      }
      incident_scale <- if (!is.null(incident_node) && v == incident_node) incident_factor else 1
      node_cap <- if (phase_green) qmax * incident_scale else 0

      S_in  <- S[ie, ncells]
      total_S <- min(sum(S_in), node_cap)
      R_out <- R[oe, 1]
      total_R <- sum(R_out)
      total_flow <- min(total_S, total_R)

      alloc_in  <- if (sum(S_in) > 0) S_in / sum(S_in) * total_flow else rep(0, length(ie))
      alloc_out <- if (sum(R_out) > 0) R_out / sum(R_out) * total_flow else rep(0, length(oe))

      exit_flow[ie]  <- exit_flow[ie]  + alloc_in
      entry_flow[oe] <- entry_flow[oe] + alloc_out
    }

    # --- source nodes: external demand feeds outgoing edges ---------------
    for (v in source_nodes) {
      oe <- out_edges_of[[v]]
      if (length(oe) == 0) next
      R_out <- R[oe, 1]
      alloc <- pmin(R_out, demand_rate / length(oe))
      entry_flow[oe] <- entry_flow[oe] + alloc
    }

    # --- sink nodes: unconstrained exit (vehicles leave the network) ------
    for (v in sink_nodes) {
      ie <- in_edges_of[[v]]
      if (length(ie) == 0) next
      exit_flow[ie] <- exit_flow[ie] + S[ie, ncells]
      cum_out <- cum_out + sum(S[ie, ncells]) * dt
    }

    # Save realised boundary flows for this completed simulation interval.
    entry_flow_hist[t + 1, ] <- entry_flow
    exit_flow_hist[t + 1, ]  <- exit_flow

    # --- update densities ---------------------------------------------------
    k_new <- k
    for (e in seq_len(E_n)) {
      inflow  <- c(entry_flow[e], if (ncells > 1) flow_internal[e, ] else numeric(0))
      outflow <- c(if (ncells > 1) flow_internal[e, ] else numeric(0), exit_flow[e])
      k_new[e, ] <- k[e, ] + dt / dx[e] * (inflow - outflow)
    }
    k_new[k_new < 0] <- 0
    k_new[k_new > kjam] <- kjam
    k <- k_new
    k_hist[t + 1, , ] <- k
    throughput[t + 1] <- cum_out
  }

  time_axis <- seq(0, nsteps) * dt

  list(fd = fd, dx = dx, dt = dt, ncells = ncells, time_axis = time_axis,
       k_hist = k_hist, throughput = throughput,
       entry_flow_hist = entry_flow_hist, exit_flow_hist = exit_flow_hist,
       source_nodes = source_nodes, sink_nodes = sink_nodes,
       junction_nodes = junction_nodes, edge_len = edge_len,
       cycle_length = cycle_length, green_split = green_split,
       signalize = signalize)
}

#' Summarise a simulation into per-edge and network-wide KPIs.
summarise_sim <- function(sim) {
  fd <- sim$fd
  k_hist <- sim$k_hist
  ncells <- sim$ncells
  nT <- dim(k_hist)[1]; E_n <- dim(k_hist)[2]

  avg_speed_t <- numeric(nT)
  veh_in_net_t <- numeric(nT)
  for (t in seq_len(nT)) {
    kt <- k_hist[t, , ]
    if (is.null(dim(kt))) kt <- matrix(kt, nrow = E_n)
    v_cells <- speed_fn(kt, fd$vf, fd$w, fd$kjam, fd$kc)
    veh_cells <- kt * matrix(sim$dx, nrow = E_n, ncol = ncells)
    veh_in_net_t[t] <- sum(veh_cells)
    tot_veh <- sum(veh_cells)
    avg_speed_t[t] <- if (tot_veh > 1e-6) sum(v_cells * veh_cells) / tot_veh else fd$vf
  }

  delay_rate <- pmax(0, veh_in_net_t * (1 / pmax(avg_speed_t, 1e-6) - 1 / fd$vf)) # veh*s per s
  cum_delay_veh_h <- cumsum(delay_rate * c(0, diff(sim$time_axis))) / 3600

  edge_avg_k <- apply(k_hist, 2, mean)
  edge_avg_v <- sapply(seq_len(E_n), function(e) {
    kt <- k_hist[, e, ]
    mean(speed_fn(kt, fd$vf, fd$w, fd$kjam, fd$kc))
  })
  edge_max_k <- apply(k_hist, 2, max)

  list(avg_speed_t = avg_speed_t, veh_in_net_t = veh_in_net_t,
       cum_delay_veh_h = cum_delay_veh_h, throughput = sim$throughput,
       edge_avg_k = edge_avg_k, edge_avg_v = edge_avg_v, edge_max_k = edge_max_k)
}

# ============================================================================
# 4. UI — Modern research dashboard inspired by the supplied HTML template
# ============================================================================

ui <- dashboardPage(

  # Keep the shinydashboard shell for its tab machinery, but visually replace it
  # with a clean, research-dashboard interface.
  dashboardHeader(title = NULL),

  dashboardSidebar(
    width = 235,
    sidebarMenu(
      id = "tabs",
      menuItem("Home", tabName = "home"),
      menuItem("Model", tabName = "model"),
      menuItem("Setup", tabName = "setup"),
      menuItem("Network", tabName = "network"),
      menuItem("Results", tabName = "results"),
      menuItem("About", tabName = "about")
    )
  ),

  dashboardBody(

    tags$head(
      tags$link(rel = "preconnect", href = "https://fonts.googleapis.com"),
      tags$link(rel = "preconnect", href = "https://fonts.gstatic.com", crossorigin = "anonymous"),
      tags$link(
        href = "https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,400;9..144,500;9..144,600&family=Inter:wght@300;400;500;600;700&display=swap",
        rel = "stylesheet"
      ),
      tags$style(HTML('
        :root {
          --lift-bg: #f1e9da;
          --lift-ink: #182d23;
          --lift-soft: #3a3a34;
          --lift-faint: #787265;
          --lift-accent: #bb3f17;
          --lift-warm: #e0652e;
          --lift-teal: #6894a4;
          --lift-green: #7eb997;
          --lift-edge: #a69d90;
          --lift-white: #ffffff;
          --lift-border: #d6cdbf;
        }

        html, body, .content-wrapper, .right-side, .main-footer {
          background: var(--lift-bg) !important;
          font-family: "Inter", sans-serif !important;
          color: var(--lift-ink) !important;
        }

        * { box-sizing: border-box; }

        /* Remove the stock dashboard chrome while retaining its tab system. */
        .main-header, .main-sidebar { display: none !important; }
        .content-wrapper, .right-side { margin-left: 0 !important; }
        .main-footer { display: none !important; }
        .content { padding: 0 2px 28px !important; }

        /* Outer app container
           Wide-screen layout: use nearly the full browser width instead of
           capping the dashboard at 1240px. The small outer gutter keeps cards
           away from the browser edge without creating large dead side-space. */
        .lift-shell {
          width: 100%;
          max-width: 1920px;
          margin: 0 auto;
          padding: 24px clamp(14px, 1.8vw, 32px) 10px;
        }

        /* Ensure the hidden shinydashboard shell never constrains the custom UI. */
        .content-wrapper,
        .right-side,
        .content {
          width: 100% !important;
          max-width: none !important;
        }

        /* Header */
        .lift-header {
          margin-bottom: 22px;
          border-bottom: 1px solid var(--lift-ink);
          padding-bottom: 16px;
        }
        .lift-header-top {
          display: flex;
          justify-content: space-between;
          gap: 16px;
          align-items: baseline;
          border-bottom: 1px solid var(--lift-ink);
          padding-bottom: 8px;
          margin-bottom: 9px;
        }
        .lift-eyebrow {
          font-size: 9px;
          letter-spacing: .19em;
          text-transform: uppercase;
          color: var(--lift-faint);
        }
        .lift-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 44px;
          font-weight: 600;
          line-height: 1;
          letter-spacing: -.035em;
          margin: 8px 0 6px;
          color: var(--lift-ink);
        }
        .lift-title span { color: var(--lift-warm); }
        .lift-subtitle {
          margin: 0;
          color: var(--lift-faint);
          font-size: 11px;
          letter-spacing: .12em;
          text-transform: uppercase;
        }

        /* Top navigation */
        .lift-nav {
          display: flex;
          gap: 3px;
          flex-wrap: wrap;
          margin-bottom: 22px;
          padding: 4px;
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
        }
        .lift-nav-link {
          display: inline-flex;
          align-items: center;
          gap: 7px;
          padding: 9px 13px;
          border-radius: 6px;
          color: var(--lift-faint) !important;
          background: transparent;
          text-decoration: none !important;
          font-size: 11px;
          font-weight: 600;
          letter-spacing: .02em;
          transition: all .18s ease;
        }
        .lift-nav-link:hover { color: var(--lift-ink) !important; background: #f6f1e8; }
        .lift-nav-link.active { color: var(--lift-bg) !important; background: var(--lift-ink); }

        /* Shared card system */
        .lift-card {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 20px;
          box-shadow: none;
        }
        .lift-card + .lift-card { margin-top: 16px; }
        .lift-card-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 20px;
          line-height: 1.15;
          font-weight: 500;
          color: var(--lift-ink);
          margin: 0 0 4px;
        }
        .lift-card-subtitle {
          font-size: 12px;
          line-height: 1.55;
          color: var(--lift-faint);
          margin: 0 0 16px;
        }
        .lift-section-kicker {
          font-size: 9px;
          text-transform: uppercase;
          letter-spacing: .16em;
          color: var(--lift-faint);
          margin: 0 0 7px;
          font-weight: 600;
        }

        /* Hero / overview */
        .lift-hero {
          display: grid;
          grid-template-columns: minmax(0, 1.5fr) minmax(260px, .8fr);
          gap: 18px;
          margin-bottom: 18px;
        }
        .lift-hero-main {
          background: var(--lift-ink);
          color: var(--lift-bg);
          border-radius: 8px;
          padding: 28px;
        }
        .lift-hero-main .lift-section-kicker { color: #b9c9c0; }
        .lift-hero-main h2 {
          font-family: "Fraunces", Georgia, serif;
          font-size: 31px;
          line-height: 1.06;
          font-weight: 500;
          margin: 0 0 10px;
          letter-spacing: -.02em;
        }
        .lift-hero-main p {
          color: #d7ddd8;
          max-width: 700px;
          font-size: 13px;
          line-height: 1.75;
          margin: 0;
        }
        .lift-hero-side {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 22px;
        }
        .lift-hero-side strong {
          display: block;
          font-family: "Fraunces", Georgia, serif;
          font-size: 18px;
          font-weight: 500;
          margin-bottom: 7px;
        }
        .lift-hero-side p { font-size: 12px; color: var(--lift-soft); line-height: 1.65; margin: 0; }

        /* Animated traffic scene — CSS/SVG-free so it runs inside Shiny without external assets. */
        .traffix-hero-layout {
          display: grid;
          grid-template-columns: minmax(0, 1.02fr) minmax(330px, .98fr);
          gap: 24px;
          align-items: center;
        }
        .traffix-traffic-scene {
          position: relative;
          min-height: 258px;
          border: 1px solid rgba(241,233,218,.14);
          border-radius: 9px;
          overflow: hidden;
          background:
            radial-gradient(circle at 76% 22%, rgba(126,185,151,.12), transparent 28%),
            radial-gradient(circle at 28% 70%, rgba(104,148,164,.10), transparent 32%),
            linear-gradient(160deg, #20352d 0%, #14261f 47%, #0f1b16 100%);
          box-shadow: inset 0 0 0 1px rgba(255,255,255,.025);
        }
        .traffix-scene-label {
          position: absolute;
          top: 13px;
          left: 16px;
          z-index: 8;
          font-family: Inter, sans-serif;
          font-size: 9px;
          text-transform: uppercase;
          letter-spacing: .18em;
          color: #a7b9b0;
        }
        .traffix-scene-status {
          position: absolute;
          top: 10px;
          right: 12px;
          z-index: 8;
          display: inline-flex;
          align-items: center;
          gap: 6px;
          padding: 5px 8px;
          border-radius: 999px;
          background: rgba(255,255,255,.06);
          border: 1px solid rgba(255,255,255,.1);
          font-size: 8px;
          letter-spacing: .12em;
          text-transform: uppercase;
          color: #c9d4cf;
        }
        .traffix-scene-status-dot {
          width: 6px; height: 6px; border-radius: 50%; background: var(--lift-green);
          box-shadow: 0 0 0 4px rgba(126,185,151,.08), 0 0 12px rgba(126,185,151,.45);
          animation: traffixPulse 2.2s ease-in-out infinite;
        }
        .traffix-road {
          position: absolute;
          left: -8%;
          right: -8%;
          bottom: 33px;
          height: 112px;
          transform: perspective(340px) rotateX(18deg) skewX(-7deg);
          transform-origin: 50% 100%;
          background: linear-gradient(to bottom, #27332f 0%, #1b2421 100%);
          border-top: 1px solid rgba(255,255,255,.08);
          border-bottom: 1px solid rgba(255,255,255,.10);
        }
        .traffix-road:before, .traffix-road:after {
          content: "";
          position: absolute;
          left: 0; right: 0;
          height: 2px;
          background: rgba(255,255,255,.16);
        }
        .traffix-road:before { top: 18px; }
        .traffix-road:after { bottom: 17px; }
        .traffix-lane-markings {
          position: absolute;
          left: 0; right: 0; top: 53px; height: 4px;
          background: repeating-linear-gradient(to right, rgba(241,233,218,.72) 0 42px, transparent 42px 74px);
          opacity: .72;
          animation: traffixRoadDash 1.35s linear infinite;
        }
        .traffix-road-glow {
          position: absolute;
          left: 9%; right: 11%; bottom: 53px; height: 2px;
          background: linear-gradient(to right, transparent, rgba(187,63,23,.35), rgba(126,185,151,.3), transparent);
          filter: blur(2px);
        }
        .traffix-node {
          position: absolute;
          z-index: 3;
          width: 7px; height: 7px;
          border-radius: 50%;
          border: 1px solid rgba(241,233,218,.65);
          background: #20352d;
          box-shadow: 0 0 0 5px rgba(241,233,218,.035);
          animation: traffixNodePulse 2.7s ease-in-out infinite;
        }
        .traffix-node.n1 { left: 14%; bottom: 92px; }
        .traffix-node.n2 { left: 39%; bottom: 105px; animation-delay: .5s; }
        .traffix-node.n3 { left: 64%; bottom: 86px; animation-delay: 1s; }
        .traffix-node.n4 { left: 78%; bottom: 105px; animation-delay: 1.5s; }
        .traffix-light {
          position: absolute;
          right: 13%;
          bottom: 95px;
          z-index: 7;
          width: 22px;
          height: 54px;
          padding: 4px 3px;
          border-radius: 7px;
          background: #111815;
          border: 1px solid rgba(241,233,218,.18);
          box-shadow: 0 8px 20px rgba(0,0,0,.18);
        }
        .traffix-light:before {
          content: "";
          position: absolute;
          left: 9px; bottom: -28px; width: 3px; height: 30px; background: rgba(241,233,218,.28);
        }
        .traffix-bulb {
          display: block;
          width: 8px; height: 8px;
          margin: 0 auto 3px;
          border-radius: 50%;
          background: #303733;
          box-shadow: inset 0 0 0 1px rgba(255,255,255,.06);
        }
        .traffix-bulb.red { animation: traffixRed 6.5s infinite; }
        .traffix-bulb.amber { animation: traffixAmber 6.5s infinite; }
        .traffix-bulb.green { animation: traffixGreen 6.5s infinite; }
        .traffix-car {
          position: absolute;
          z-index: 6;
          bottom: 79px;
          width: 52px;
          height: 24px;
          filter: drop-shadow(0 5px 4px rgba(0,0,0,.22));
          animation: traffixDriveStop 9s linear infinite;
        }
        .traffix-car .body {
          position: absolute;
          left: 1px; right: 1px; bottom: 3px; height: 15px;
          border-radius: 6px 7px 4px 4px;
          background: var(--lift-bg);
          border: 1px solid rgba(255,255,255,.3);
        }
        .traffix-car .cabin {
          position: absolute;
          left: 12px; top: 1px; width: 25px; height: 11px;
          border-radius: 9px 9px 2px 2px;
          background: rgba(190,211,204,.72);
          clip-path: polygon(15% 100%, 26% 7%, 74% 7%, 88% 100%);
          opacity: .8;
        }
        .traffix-car .wheel {
          position: absolute;
          bottom: 0; width: 8px; height: 8px;
          border-radius: 50%; background: #0b0f0d;
          border: 1px solid rgba(255,255,255,.18);
        }
        .traffix-car .w1 { left: 8px; }
        .traffix-car .w2 { right: 8px; }
        .traffix-car.car-orange .body { background: var(--lift-warm); }
        .traffix-car.car-teal .body { background: var(--lift-teal); }
        .traffix-car.car-green .body { background: var(--lift-green); }
        .traffix-car.car-light .body { background: #dfe5de; }
        .traffix-car.c1 { left: -60px; animation-delay: -1.6s; animation-duration: 8.2s; }
        .traffix-car.c2 { left: -120px; animation-delay: -3.2s; animation-duration: 8.8s; transform: scale(.92); }
        .traffix-car.c3 { left: -175px; animation-delay: -4.7s; animation-duration: 9.3s; transform: scale(.82); }
        .traffix-car.c4 { left: -225px; animation-delay: -6.3s; animation-duration: 8.9s; transform: scale(.88); }
        .traffix-car.c5 { left: -285px; animation-delay: -7.4s; animation-duration: 9.6s; transform: scale(.78); }
        .traffix-queue {
          position: absolute;
          left: 60%;
          bottom: 111px;
          z-index: 5;
          display: inline-flex;
          align-items: center;
          gap: 5px;
          padding: 4px 7px;
          border-radius: 999px;
          background: rgba(187,63,23,.12);
          border: 1px solid rgba(187,63,23,.3);
          color: #e9c2b4;
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .13em;
          animation: traffixQueue 6.5s ease-in-out infinite;
        }
        .traffix-queue-dot { width: 5px; height: 5px; border-radius: 50%; background: var(--lift-accent); }
        .traffix-flowline {
          position: absolute;
          left: 14px; right: 14px; bottom: 13px;
          display: flex; justify-content: space-between; align-items: center;
          color: #859890;
          font-size: 8px; text-transform: uppercase; letter-spacing: .15em;
        }
        .traffix-flowline span:nth-child(2) { color: #d8b2a5; }
        .traffix-flow-arrow { color: #9db1a8; animation: traffixArrow 1.4s ease-in-out infinite; }
        @keyframes traffixDriveStop {
          0% { left: -16%; opacity: 0; }
          8% { opacity: 1; }
          47% { left: 47%; opacity: 1; }
          54% { left: 58%; opacity: 1; }
          74% { left: 58%; opacity: 1; }
          90% { left: 108%; opacity: 1; }
          100% { left: 108%; opacity: 0; }
        }
        @keyframes traffixRoadDash { from { background-position-x: 0; } to { background-position-x: -74px; } }
        @keyframes traffixPulse { 0%,100% { opacity: .7; transform: scale(1); } 50% { opacity: 1; transform: scale(1.18); } }
        @keyframes traffixNodePulse { 0%,100% { transform: scale(1); opacity: .5; } 50% { transform: scale(1.45); opacity: 1; } }
        @keyframes traffixRed { 0%,53% { background: #303733; box-shadow: none; } 55%,77% { background: var(--lift-accent); box-shadow: 0 0 10px rgba(187,63,23,.65); } 80%,100% { background: #303733; box-shadow: none; } }
        @keyframes traffixAmber { 0%,50% { background: #303733; box-shadow: none; } 52%,54% { background: #d6a14a; box-shadow: 0 0 9px rgba(214,161,74,.55); } 56%,100% { background: #303733; box-shadow: none; } }
        @keyframes traffixGreen { 0%,50% { background: var(--lift-green); box-shadow: 0 0 10px rgba(126,185,151,.62); } 52%,79% { background: #303733; box-shadow: none; } 81%,100% { background: var(--lift-green); box-shadow: 0 0 10px rgba(126,185,151,.62); } }
        @keyframes traffixQueue { 0%,49% { opacity: 0; transform: translateY(4px); } 52%,76% { opacity: 1; transform: translateY(0); } 82%,100% { opacity: 0; transform: translateY(-3px); } }
        @keyframes traffixArrow { 0%,100% { transform: translateX(0); opacity: .6; } 50% { transform: translateX(5px); opacity: 1; } }
        @media (prefers-reduced-motion: reduce) {
          .traffix-traffic-scene * { animation: none !important; }
        }

        /* KPI cards */
        .lift-kpis { display: flex; gap: 12px; flex-wrap: wrap; margin-bottom: 18px; }
        .lift-kpi {
          flex: 1 1 180px;
          min-width: 170px;
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 16px 19px;
          border-top: 3px solid var(--lift-accent);
        }
        .lift-kpi.teal { border-top-color: var(--lift-teal); }
        .lift-kpi.green { border-top-color: var(--lift-green); }
        .lift-kpi.warm { border-top-color: var(--lift-warm); }
        .lift-kpi-label {
          font-size: 10px;
          text-transform: uppercase;
          letter-spacing: .14em;
          color: var(--lift-faint);
          margin-bottom: 4px;
        }
        .lift-kpi-value {
          font-family: "Fraunces", Georgia, serif;
          font-size: 25px;
          font-weight: 600;
          letter-spacing: -.02em;
          color: var(--lift-ink);
          line-height: 1.1;
        }
        .lift-kpi-sub { font-size: 11px; color: var(--lift-faint); margin-top: 4px; }

        /* 2-column cards */
        .lift-grid-2 {
          display: grid;
          grid-template-columns: minmax(0, 1fr) minmax(0, 1fr);
          gap: 16px;
          margin-bottom: 16px;
        }
        .lift-grid-3 {
          display: grid;
          grid-template-columns: repeat(3, minmax(0, 1fr));
          gap: 16px;
          margin-bottom: 16px;
        }

        /* Forms */
        .lift-form-grid {
          display: grid;
          grid-template-columns: repeat(2, minmax(0, 1fr));
          gap: 17px;
        }
        .lift-field-label {
          font-size: 10px;
          color: var(--lift-faint);
          text-transform: uppercase;
          letter-spacing: .12em;
          margin-bottom: 5px;
        }
        .lift-control .form-control, .lift-control .selectize-input,
        .lift-control input, .lift-control select {
          border: 1px solid var(--lift-border) !important;
          border-radius: 6px !important;
          background: var(--lift-bg) !important;
          box-shadow: none !important;
          color: var(--lift-ink) !important;
          font-family: "Inter", sans-serif !important;
          font-size: 13px !important;
        }
        .lift-control .form-group { margin-bottom: 0; }
        .lift-control .shiny-input-container { width: 100% !important; }
        .lift-control .irs { margin-top: 4px; }
        .lift-control .irs-bar, .lift-control .irs-single, .lift-control .irs-from, .lift-control .irs-to {
          background: var(--lift-accent) !important;
          border-color: var(--lift-accent) !important;
        }
        .lift-control .irs-line { background: #d9d0c2 !important; border-color: #d9d0c2 !important; }
        .lift-control .checkbox label { color: var(--lift-soft); font-size: 12px; }

        /* Streamlined Simulation Setup */
        .setup-intro {
          display: flex;
          align-items: center;
          justify-content: space-between;
          gap: 18px;
          margin-bottom: 16px;
          padding: 18px 20px;
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          background: var(--lift-white);
        }
        .setup-intro-copy { min-width: 0; }
        .setup-intro-copy .lift-card-title { margin-bottom: 5px; }
        .setup-intro-copy .lift-card-subtitle { margin-bottom: 0; max-width: 72ch; }
        .setup-live-badge {
          flex: 0 0 auto;
          display: inline-flex;
          align-items: center;
          gap: 7px;
          padding: 7px 10px;
          border-radius: 999px;
          border: 1px solid rgba(126,185,151,.45);
          background: rgba(126,185,151,.10);
          color: var(--lift-ink);
          font-size: 9px;
          font-weight: 700;
          letter-spacing: .11em;
          text-transform: uppercase;
          white-space: nowrap;
        }
        .setup-live-dot {
          width: 7px;
          height: 7px;
          border-radius: 50%;
          background: var(--lift-green);
          box-shadow: 0 0 0 4px rgba(126,185,151,.12);
        }
        .setup-parameter-grid {
          display: grid;
          grid-template-columns: repeat(2, minmax(0, 1fr));
          gap: 16px;
          margin-bottom: 16px;
        }
        .setup-parameter-card {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 22px;
          min-width: 0;
        }
        .setup-parameter-card.geometry { border-top: 3px solid var(--lift-teal); }
        .setup-parameter-card.response { border-top: 3px solid var(--lift-accent); }
        .setup-parameter-card .lift-card-subtitle { margin-bottom: 20px; }
        .setup-control-block {
          padding: 15px 0 17px;
          border-top: 1px solid #ebe4d8;
        }
        .setup-control-block:first-of-type {
          border-top: 0;
          padding-top: 2px;
        }
        .setup-control-block:last-child { padding-bottom: 2px; }
        .setup-control-block .control-label {
          display: block;
          color: var(--lift-ink) !important;
          font-size: 12px !important;
          font-weight: 700 !important;
          margin-bottom: 3px !important;
        }
        .setup-param-help {
          margin: 0 0 7px;
          color: var(--lift-faint);
          font-size: 10.5px;
          line-height: 1.5;
        }
        .setup-parameter-card .irs {
          margin-top: 2px !important;
          margin-bottom: 0 !important;
        }
        .setup-parameter-card .irs-min,
        .setup-parameter-card .irs-max {
          color: var(--lift-faint) !important;
          background: transparent !important;
          font-size: 9px !important;
        }
        .setup-parameter-card .irs-single {
          font-weight: 700 !important;
          border-radius: 4px !important;
        }
        .setup-summary {
          display: grid;
          grid-template-columns: minmax(0, 1.15fr) minmax(260px, .85fr);
          gap: 16px;
          margin-bottom: 0;
        }
        .setup-derived {
          background: var(--lift-ink);
          border-radius: 8px;
          padding: 22px;
          color: var(--lift-bg);
        }
        .setup-derived .lift-section-kicker { color: #b9c9c0; }
        .setup-derived-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 20px;
          font-weight: 500;
          margin: 0 0 15px;
          color: var(--lift-bg);
        }
        .setup-derived-grid {
          display: grid;
          grid-template-columns: repeat(3, minmax(0, 1fr));
          gap: 10px;
        }
        .setup-derived-item {
          padding: 12px;
          border: 1px solid rgba(241,233,218,.14);
          border-radius: 7px;
          background: rgba(255,255,255,.035);
        }
        .setup-derived-label {
          color: #aebdb5;
          font-size: 8.5px;
          letter-spacing: .12em;
          text-transform: uppercase;
          margin-bottom: 4px;
        }
        .setup-derived-value {
          font-family: "Fraunces", Georgia, serif;
          color: #f1e9da;
          font-size: 17px;
          line-height: 1.2;
        }
        .setup-assumptions {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 22px;
        }
        .setup-assumption-row {
          display: flex;
          align-items: baseline;
          justify-content: space-between;
          gap: 14px;
          padding: 8px 0;
          border-bottom: 1px solid #ebe4d8;
          font-size: 11px;
        }
        .setup-assumption-row:last-child { border-bottom: 0; }
        .setup-assumption-name { color: var(--lift-faint); }
        .setup-assumption-value { color: var(--lift-ink); font-weight: 700; text-align: right; }
        .setup-auto-note {
          margin-top: 14px;
          padding: 11px 13px;
          border-left: 3px solid var(--lift-green);
          border-radius: 0 6px 6px 0;
          background: rgba(126,185,151,.09);
          color: var(--lift-ink);
          font-size: 10.5px;
          line-height: 1.55;
        }

        /* Buttons */
        .lift-run-wrap {
          display: flex;
          align-items: center;
          justify-content: space-between;
          gap: 14px;
          padding: 18px 20px;
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          background: rgba(255,255,255,.62);
          margin-top: 16px;
        }
        .lift-run-note { font-size: 11px; color: var(--lift-faint); line-height: 1.5; }
        .btn-lift-run {
          background: var(--lift-ink) !important;
          color: var(--lift-bg) !important;
          border: 0 !important;
          border-radius: 6px !important;
          padding: 11px 21px !important;
          font-size: 12px !important;
          font-weight: 700 !important;
          letter-spacing: .04em !important;
          box-shadow: none !important;
        }
        .btn-lift-run:hover { background: var(--lift-accent) !important; }
        .btn-lift-secondary {
          background: transparent !important;
          color: var(--lift-ink) !important;
          border: 1px solid var(--lift-ink) !important;
          border-radius: 6px !important;
        }
        .lift-network-toolbar {
          display: flex;
          align-items: flex-end;
          gap: 10px;
          margin-bottom: 12px;
          flex-wrap: wrap;
        }
        .lift-network-toolbar .shiny-input-container {
          margin-bottom: 0 !important;
        }
        .lift-network-toolbar .form-group {
          margin-bottom: 0 !important;
        }
        .lift-network-toolbar .control-label {
          font-size: 9px !important;
          text-transform: uppercase !important;
          letter-spacing: .12em !important;
          color: var(--lift-faint) !important;
          margin-bottom: 5px !important;
        }
        .lift-network-canvas {
          background: #fbf8f1;
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          overflow: hidden;
          min-height: 560px;
        }
        .lift-network-canvas .vis-network {
          outline: none !important;
        }
        .lift-network-summary {
          display: grid;
          grid-template-columns: repeat(3, minmax(0,1fr));
          gap: 8px;
          margin-top: 12px;
        }
        .lift-network-stat {
          background: var(--lift-bg);
          border: 1px solid var(--lift-border);
          border-radius: 6px;
          padding: 10px 12px;
        }
        .lift-network-stat-label {
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .12em;
          color: var(--lift-faint);
          margin-bottom: 3px;
        }
        .lift-network-stat-value {
          font-family: "Fraunces", Georgia, serif;
          font-size: 17px;
          color: var(--lift-ink);
          font-weight: 500;
        }
        .lift-network-selection {
          min-height: 220px;
          padding: 14px;
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          background: var(--lift-bg);
        }
        .lift-network-selection-empty {
          min-height: 190px;
          display: flex;
          align-items: center;
          justify-content: center;
          text-align: center;
          color: var(--lift-faint);
          font-family: "Fraunces", Georgia, serif;
          font-size: 14px;
          line-height: 1.5;
        }
        .lift-network-selection-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 19px;
          font-weight: 500;
          color: var(--lift-ink);
          margin-bottom: 12px;
        }
        .lift-network-detail-grid {
          display: grid;
          grid-template-columns: 1fr 1fr;
          gap: 11px;
        }
        .lift-network-detail-label {
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .1em;
          color: var(--lift-faint);
          margin-bottom: 3px;
        }
        .lift-network-detail-value {
          font-size: 12px;
          font-weight: 600;
          color: var(--lift-ink);
        }
        .lift-network-legend {
          margin-top: 12px;
          padding: 11px 13px;
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          background: rgba(255,255,255,.72);
        }
        .lift-network-gradient {
          height: 7px;
          border-radius: 999px;
          margin: 7px 0 4px;
          background: linear-gradient(to right, #2ECC71, #F5A623, #E63946);
        }
        .lift-network-gradient.reverse {
          background: linear-gradient(to right, #E63946, #F5A623, #2ECC71);
        }
        .lift-network-legend-row {
          display: flex;
          justify-content: space-between;
          gap: 10px;
          font-size: 9px;
          color: var(--lift-faint);
        }
        @media (max-width: 640px) {
          .lift-network-summary { grid-template-columns: 1fr; }
          .lift-network-detail-grid { grid-template-columns: 1fr; }
        }

        /* Redesigned top network section */
        .network-top-stage {
          display: grid;
          grid-template-columns: minmax(0, 1.35fr) minmax(320px, .95fr);
          gap: 16px;
          margin-bottom: 16px;
        }
        .network-top-hero {
          background: linear-gradient(135deg, #0f3027 0%, #12382c 50%, #173d31 100%);
          border-radius: 8px;
          padding: 28px 30px;
          color: var(--lift-bg);
          border: 1px solid rgba(24,45,35,.18);
          min-width: 0;
          box-shadow: inset 0 1px 0 rgba(255,255,255,.04);
        }
        .network-top-hero .lift-section-kicker {
          color: #b7c8bf;
          margin-bottom: 10px;
        }
        .network-top-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 22px;
          line-height: 1.2;
          letter-spacing: -.02em;
          margin: 0 0 10px;
          color: var(--lift-bg);
        }
        .network-top-copy {
          color: rgba(241,233,218,.92);
          font-size: 13px;
          line-height: 1.75;
          max-width: 60ch;
          margin: 0 0 18px;
        }
        .network-story-band {
          display: grid;
          grid-template-columns: repeat(3, minmax(0,1fr));
          gap: 10px;
          margin-bottom: 18px;
        }
        .network-story-card {
          background: rgba(255,255,255,.06);
          border: 1px solid rgba(241,233,218,.10);
          border-radius: 8px;
          padding: 13px 14px;
          min-width: 0;
        }
        .network-story-label {
          color: #b4c4bc;
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .14em;
          margin-bottom: 4px;
        }
        .network-story-value {
          font-family: "Fraunces", Georgia, serif;
          color: #f1e9da;
          font-size: 18px;
          line-height: 1.15;
        }
        .network-story-sub {
          color: rgba(241,233,218,.78);
          font-size: 10px;
          margin-top: 4px;
          line-height: 1.45;
        }
        .network-guidance {
          display: grid;
          grid-template-columns: 1.05fr .95fr;
          gap: 12px;
          align-items: stretch;
        }
        .network-guidance-box {
          padding: 14px 15px;
          border-radius: 8px;
          background: rgba(255,255,255,.055);
          border: 1px solid rgba(241,233,218,.10);
        }
        .network-guidance-title {
          color: #f1e9da;
          font-size: 10px;
          text-transform: uppercase;
          letter-spacing: .14em;
          margin-bottom: 6px;
          font-weight: 700;
        }
        .network-guidance-text {
          color: rgba(241,233,218,.88);
          font-size: 11px;
          line-height: 1.65;
        }
        .network-phase-box {
          padding: 14px 15px;
          border-radius: 8px;
          background: rgba(187,63,23,.10);
          border: 1px solid rgba(187,63,23,.26);
        }
        .network-phase-box .lift-readout {
          margin: 0;
          padding: 0;
          border: 0;
          background: transparent;
          color: #f1e9da;
        }
        .network-phase-box .lift-readout * {
          color: #f1e9da !important;
        }
        .network-top-panel {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 22px;
          min-width: 0;
        }
        .network-panel-block {
          padding-bottom: 16px;
          margin-bottom: 16px;
          border-bottom: 1px solid #ebe4d8;
        }
        .network-panel-block:last-child {
          padding-bottom: 0;
          margin-bottom: 0;
          border-bottom: 0;
        }
        .network-panel-title {
          font-family: "Fraunces", Georgia, serif;
          color: var(--lift-ink);
          font-size: 19px;
          line-height: 1.2;
          margin: 0 0 6px;
        }
        .network-panel-copy {
          color: var(--lift-faint);
          font-size: 11px;
          line-height: 1.65;
          margin: 0 0 12px;
        }
        .network-control-row {
          display: flex;
          gap: 10px;
          align-items: flex-end;
          flex-wrap: wrap;
        }
        .network-control-row .shiny-input-container {
          margin-bottom: 0 !important;
          flex: 1 1 220px;
          min-width: 180px;
        }
        .network-time-wrap .lift-control {
          margin-bottom: 8px;
        }
        .network-diagram-shell {
          margin-bottom: 16px;
        }
        .network-diagram-header {
          display: flex;
          align-items: flex-end;
          justify-content: space-between;
          gap: 18px;
          flex-wrap: wrap;
          margin-bottom: 14px;
        }
        .network-diagram-meta {
          display: inline-flex;
          gap: 8px;
          align-items: center;
          flex-wrap: wrap;
        }
        .network-meta-pill {
          display: inline-flex;
          align-items: center;
          gap: 7px;
          padding: 6px 10px;
          border-radius: 999px;
          border: 1px solid var(--lift-border);
          background: rgba(241,233,218,.55);
          color: var(--lift-soft);
          font-size: 9px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .10em;
          white-space: nowrap;
        }
        .network-meta-dot {
          width: 7px;
          height: 7px;
          border-radius: 50%;
          background: var(--lift-accent);
        }
        .network-meta-dot.teal { background: var(--lift-teal); }
        .network-meta-dot.green { background: var(--lift-green); }
        .network-diagram-callout {
          margin-top: 12px;
          padding: 11px 13px;
          border-left: 3px solid var(--lift-accent);
          border-radius: 0 6px 6px 0;
          background: rgba(187,63,23,.07);
          color: var(--lift-ink);
          font-size: 10.5px;
          line-height: 1.6;
        }
        @media (max-width: 980px) {
          .network-top-stage,
          .network-guidance {
            grid-template-columns: 1fr;
          }
          .network-story-band {
            grid-template-columns: 1fr;
          }
        }


        /* Methods-inspired TraffiX corridor schematic */
        .network-method-card {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 24px;
          margin-bottom: 16px;
          overflow: hidden;
        }
        .network-method-head {
          display: flex;
          justify-content: space-between;
          align-items: flex-start;
          gap: 18px;
          margin-bottom: 16px;
        }
        .network-method-head-copy {
          min-width: 0;
          max-width: 760px;
        }
        .network-method-badge {
          flex: 0 0 auto;
          display: inline-flex;
          align-items: center;
          gap: 7px;
          padding: 7px 10px;
          border-radius: 999px;
          background: rgba(104,148,164,.10);
          border: 1px solid rgba(104,148,164,.30);
          color: var(--lift-ink);
          font-size: 8.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .11em;
          white-space: nowrap;
        }
        .network-method-badge-dot {
          width: 7px;
          height: 7px;
          border-radius: 50%;
          background: var(--lift-teal);
        }
        .network-method-stage {
          border-radius: 9px;
          overflow-x: auto;
          overflow-y: hidden;
          background:
            linear-gradient(rgba(255,255,255,.022) 1px, transparent 1px),
            linear-gradient(90deg, rgba(255,255,255,.022) 1px, transparent 1px),
            linear-gradient(135deg, #102f27 0%, #14372d 100%);
          background-size: 28px 28px, 28px 28px, auto;
          border: 1px solid rgba(24,45,35,.22);
          padding: 20px 18px 16px;
        }
        .network-method-stage-inner {
          min-width: 980px;
        }
        .network-method-flowbar {
          display: flex;
          justify-content: space-between;
          align-items: center;
          margin: 0 28px 16px;
          gap: 16px;
        }
        .network-method-flowlabel {
          display: inline-flex;
          align-items: center;
          gap: 8px;
          color: #d7e0db;
          font-size: 8.5px;
          text-transform: uppercase;
          letter-spacing: .13em;
          font-weight: 700;
        }
        .network-method-flowline {
          width: 48px;
          height: 1px;
          background: rgba(241,233,218,.40);
          position: relative;
        }
        .network-method-flowline.forward::after {
          content: "";
          position: absolute;
          right: -1px;
          top: -3px;
          border-left: 6px solid #7eb997;
          border-top: 3px solid transparent;
          border-bottom: 3px solid transparent;
        }
        .network-method-flowline.backward::before {
          content: "";
          position: absolute;
          left: -1px;
          top: -3px;
          border-right: 6px solid #e0652e;
          border-top: 3px solid transparent;
          border-bottom: 3px solid transparent;
        }
        .network-method-track {
          display: grid;
          grid-template-columns:
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px minmax(70px,1fr)
            64px;
          align-items: center;
          padding: 18px 12px 8px;
        }
        .network-method-node {
          position: relative;
          display: flex;
          flex-direction: column;
          align-items: center;
          z-index: 2;
        }
        .network-method-node-circle {
          width: 46px;
          height: 46px;
          border-radius: 50%;
          display: flex;
          align-items: center;
          justify-content: center;
          border: 2px solid rgba(255,255,255,.88);
          color: #fff;
          font-family: "Fraunces", Georgia, serif;
          font-size: 15px;
          font-weight: 600;
          box-shadow: 0 0 0 7px rgba(255,255,255,.045);
        }
        .network-method-node.source .network-method-node-circle { background: #0fb5ae; }
        .network-method-node.junction .network-method-node-circle { background: #2f6d58; }
        .network-method-node.signal .network-method-node-circle {
          background: #bb3f17;
          box-shadow: 0 0 0 7px rgba(187,63,23,.13);
        }
        .network-method-node.sink .network-method-node-circle { background: #8e44ad; }
        .network-method-node-name {
          margin-top: 8px;
          color: #f1e9da;
          font-size: 9px;
          font-weight: 700;
          letter-spacing: .07em;
          text-transform: uppercase;
          white-space: nowrap;
        }
        .network-method-node-role {
          margin-top: 2px;
          color: #9fb1a8;
          font-size: 8px;
          white-space: nowrap;
        }
        .network-method-link {
          height: 7px;
          border-radius: 999px;
          position: relative;
          background: linear-gradient(90deg, #7eb997 0%, #7eb997 100%);
          box-shadow: 0 0 0 3px rgba(126,185,151,.06);
        }
        .network-method-link::after {
          content: "";
          position: absolute;
          right: -1px;
          top: -3px;
          border-left: 7px solid currentColor;
          border-top: 6px solid transparent;
          border-bottom: 6px solid transparent;
          color: #7eb997;
        }
        .network-method-link.moderate {
          background: linear-gradient(90deg, #7eb997, #e5aa49);
          color: #e5aa49;
        }
        .network-method-link.congested {
          background: linear-gradient(90deg, #e5aa49, #d94b3c);
          color: #d94b3c;
          height: 9px;
        }
        .network-method-link.recovery {
          background: linear-gradient(90deg, #d94b3c, #7eb997);
          color: #7eb997;
        }
        .network-method-link-label {
          position: absolute;
          left: 50%;
          transform: translateX(-50%);
          top: -23px;
          color: #b9c8c0;
          font-size: 8px;
          letter-spacing: .08em;
          font-weight: 700;
          text-transform: uppercase;
          white-space: nowrap;
        }
        .network-method-wave {
          margin: 17px auto 4px;
          width: 48%;
          padding: 7px 10px;
          border-radius: 999px;
          border: 1px dashed rgba(224,101,46,.55);
          color: #efb195;
          background: rgba(224,101,46,.07);
          text-align: center;
          font-size: 8.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .10em;
        }
        .network-method-legend {
          display: flex;
          justify-content: center;
          flex-wrap: wrap;
          gap: 16px;
          margin-top: 12px;
          color: #afbeb6;
          font-size: 8.5px;
        }
        .network-method-legend-item {
          display: inline-flex;
          align-items: center;
          gap: 6px;
        }
        .network-method-legend-dot {
          width: 8px;
          height: 8px;
          border-radius: 50%;
          background: #7eb997;
        }
        .network-method-legend-dot.orange { background: #bb3f17; }
        .network-method-legend-dot.purple { background: #8e44ad; }
        .network-method-legend-line {
          width: 24px;
          height: 5px;
          border-radius: 999px;
          background: linear-gradient(90deg,#7eb997,#d94b3c);
        }
        .network-method-steps {
          display: grid;
          grid-template-columns: repeat(4, minmax(0,1fr));
          gap: 10px;
          margin-top: 14px;
        }
        .network-method-step {
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          padding: 13px 14px;
          background: #fbf8f1;
        }
        .network-method-step-number {
          width: 24px;
          height: 24px;
          border-radius: 50%;
          display: inline-flex;
          align-items: center;
          justify-content: center;
          margin-bottom: 8px;
          background: var(--lift-ink);
          color: var(--lift-bg);
          font-family: "Fraunces", Georgia, serif;
          font-size: 11px;
          font-weight: 600;
        }
        .network-method-step-title {
          color: var(--lift-ink);
          font-size: 11px;
          font-weight: 700;
          margin-bottom: 3px;
        }
        .network-method-step-copy {
          color: var(--lift-faint);
          font-size: 9.8px;
          line-height: 1.55;
        }
        .network-workbench {
          display: grid;
          grid-template-columns: minmax(0,1.55fr) minmax(300px,.7fr);
          gap: 16px;
          margin-bottom: 16px;
        }
        .network-workbench-side {
          display: flex;
          flex-direction: column;
          gap: 16px;
          min-width: 0;
        }
        .network-live-strip {
          display: grid;
          grid-template-columns: repeat(3,minmax(0,1fr));
          gap: 8px;
          margin-bottom: 12px;
        }
        .network-live-stat {
          padding: 10px 12px;
          border-radius: 6px;
          background: var(--lift-bg);
          border: 1px solid var(--lift-border);
        }
        .network-live-stat-label {
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .11em;
          color: var(--lift-faint);
          margin-bottom: 3px;
        }
        .network-live-stat-value {
          font-family: "Fraunces", Georgia, serif;
          font-size: 16px;
          color: var(--lift-ink);
        }
        @media (max-width: 980px) {
          .network-method-steps,
          .network-workbench {
            grid-template-columns: 1fr;
          }
          .network-method-head {
            flex-direction: column;
          }
        }
        @media (max-width: 640px) {
          .network-live-strip { grid-template-columns: 1fr; }
        }


        /* Corridor playback controls — drives the Pretoria map directly */
        .corridor-playback-card {
          display: grid;
          grid-template-columns: minmax(230px,.72fr) minmax(250px,.78fr) minmax(360px,1.5fr);
          gap: 18px;
          align-items: stretch;
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 20px 22px;
          margin-bottom: 16px;
        }
        .corridor-playback-intro {
          padding-right: 4px;
        }
        .corridor-playback-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 19px;
          line-height: 1.2;
          color: var(--lift-ink);
          margin: 0 0 7px;
        }
        .corridor-playback-copy {
          font-size: 10.8px;
          line-height: 1.62;
          color: var(--lift-faint);
          margin: 0;
        }
        .corridor-playback-block {
          border-left: 1px solid #e8dfd1;
          padding-left: 18px;
          min-width: 0;
        }
        .corridor-playback-label {
          font-size: 8.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .13em;
          color: var(--lift-faint);
          margin-bottom: 7px;
        }
        .corridor-playback-block .shiny-input-container,
        .corridor-playback-block .form-group {
          margin-bottom: 0 !important;
          width: 100% !important;
        }
        .corridor-playback-block .control-label {
          display: none !important;
        }
        .corridor-playback-time {
          display: grid;
          grid-template-columns: minmax(0,1fr) auto;
          gap: 14px;
          align-items: end;
        }
        .corridor-playback-slider {
          min-width: 0;
        }
        .corridor-playback-toggle {
          min-width: 175px;
          padding-bottom: 4px;
        }
        .corridor-playback-toggle .checkbox {
          margin-top: 0 !important;
          margin-bottom: 0 !important;
        }
        .corridor-playback-toggle .checkbox label {
          color: var(--lift-ink) !important;
          font-size: 10.5px !important;
          font-weight: 700;
          white-space: nowrap;
        }
        .corridor-playback-readout {
          margin-top: 11px;
          padding: 9px 11px;
          border-radius: 6px;
          border-left: 3px solid var(--lift-accent);
          background: rgba(187,63,23,.055);
          color: var(--lift-ink);
          font-size: 10px;
          line-height: 1.5;
        }
        .corridor-playback-readout .lift-readout {
          margin: 0;
          padding: 0;
          border: 0;
          background: transparent;
          min-height: 0;
        }
        .corridor-playback-note {
          display: inline-flex;
          align-items: center;
          gap: 7px;
          margin-top: 9px;
          color: var(--lift-faint);
          font-size: 9px;
          line-height: 1.45;
        }
        .corridor-playback-dot {
          width: 7px;
          height: 7px;
          border-radius: 50%;
          background: var(--lift-green);
          box-shadow: 0 0 0 4px rgba(126,185,151,.12);
          flex: 0 0 7px;
        }
        @media (max-width: 1050px) {
          .corridor-playback-card {
            grid-template-columns: 1fr 1fr;
          }
          .corridor-playback-card > :last-child {
            grid-column: 1 / -1;
            border-left: 0;
            border-top: 1px solid #e8dfd1;
            padding-left: 0;
            padding-top: 16px;
          }
        }
        @media (max-width: 700px) {
          .corridor-playback-card {
            grid-template-columns: 1fr;
          }
          .corridor-playback-block {
            border-left: 0;
            border-top: 1px solid #e8dfd1;
            padding-left: 0;
            padding-top: 16px;
          }
          .corridor-playback-card > :last-child {
            grid-column: auto;
          }
          .corridor-playback-time {
            grid-template-columns: 1fr;
          }
          .corridor-playback-toggle {
            min-width: 0;
          }
        }

        /* Lynnwood Road traffic map */
        .lift-map-layout {
          display: grid;
          grid-template-columns: minmax(0, 2.15fr) minmax(270px, .85fr);
          gap: 16px;
          margin-bottom: 16px;
        }
        .lift-map-frame {
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          overflow: hidden;
          background: #eef0ec;
        }
        .lift-map-frame .leaflet-container {
          font-family: "Inter", sans-serif !important;
          background: #eef0ec !important;
        }
        .lift-map-frame .leaflet-control-attribution {
          background: rgba(255,255,255,.88) !important;
          color: var(--lift-faint) !important;
          font-size: 9px !important;
        }
        .lift-map-frame .leaflet-bar a {
          color: var(--lift-ink) !important;
          background: var(--lift-white) !important;
          border-color: var(--lift-border) !important;
        }

        /* Live traffic layers are restyled in place (never cleared/redrawn), and
           colour / width changes are eased so congestion fades smoothly between
           animation frames instead of snapping. */
        .lift-map-frame .traffix-live-shape {
          transition: stroke 0.12s linear, stroke-width 0.12s linear,
                      fill 0.12s linear;
        }
        .lift-map-frame .leaflet-tooltip {
          border: 1px solid var(--lift-border) !important;
          border-radius: 6px !important;
          box-shadow: none !important;
          color: var(--lift-ink) !important;
          font-size: 11px !important;
          line-height: 1.45 !important;
        }
        .lift-map-footer {
          text-align: center;
          margin-top: 9px;
          color: var(--lift-edge);
          font-size: 9px;
          letter-spacing: .22em;
          text-transform: uppercase;
        }
        .lift-map-side {
          display: flex;
          flex-direction: column;
          gap: 16px;
          min-width: 0;
        }
        .lift-map-side .lift-card + .lift-card { margin-top: 0; }
        .lift-map-selection {
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          padding: 14px;
          background: var(--lift-bg);
          min-height: 180px;
        }
        .lift-map-selection.empty {
          display: flex;
          align-items: center;
          justify-content: center;
          text-align: center;
          color: var(--lift-faint);
          font-family: "Fraunces", Georgia, serif;
          font-size: 14px;
          line-height: 1.5;
        }
        .lift-map-chip {
          display: inline-flex;
          align-items: center;
          gap: 7px;
          padding: 5px 8px;
          border: 1px solid var(--lift-border);
          border-radius: 999px;
          font-size: 9px;
          letter-spacing: .08em;
          text-transform: uppercase;
          color: var(--lift-faint);
          background: rgba(255,255,255,.72);
          margin-bottom: 10px;
        }
        .lift-map-dot {
          width: 8px;
          height: 8px;
          border-radius: 50%;
          flex: 0 0 8px;
        }
        .lift-map-key-row {
          display: grid;
          grid-template-columns: 16px 1fr;
          gap: 9px;
          align-items: start;
          margin-bottom: 10px;
          font-size: 11px;
          color: var(--lift-soft);
          line-height: 1.5;
        }
        .lift-map-key-line {
          height: 5px;
          border-radius: 999px;
          margin-top: 6px;
          background: linear-gradient(to right, #2ECC71, #F5A623, #E63946);
        }
        @media (max-width: 900px) {
          .lift-map-layout { grid-template-columns: 1fr; }
        }

        /* Tables */
        .lift-table { width: 100%; border-collapse: collapse; font-size: 12px; }
        .lift-table th {
          padding: 9px 10px;
          text-align: left;
          color: var(--lift-faint);
          font-size: 9px;
          text-transform: uppercase;
          letter-spacing: .1em;
          border-bottom: 2px solid var(--lift-border);
          font-weight: 600;
        }
        .lift-table td { padding: 9px 10px; border-bottom: 1px solid var(--lift-border); }

        /* Callouts / model notes */
        .lift-callout {
          padding: 13px 16px;
          border-left: 4px solid var(--lift-accent);
          background: rgba(187,63,23,.055);
          border-radius: 0 7px 7px 0;
          color: var(--lift-soft);
          font-size: 12px;
          line-height: 1.65;
          margin-top: 14px;
        }
        .lift-callout.teal { border-left-color: var(--lift-accent); background: rgba(187,63,23,.07); color: #f1e9da !important; }
        .lift-callout.teal strong { color: #f1e9da !important; }
        .lift-hero-main .lift-callout.teal { color: #f1e9da !important; }
        .lift-hero-main .lift-callout.teal strong { color: #f1e9da !important; }
        .lift-callout.green { border-left-color: var(--lift-green); background: rgba(126,185,151,.08); }
        .lift-callout.model-transfer {
          border-left-color: var(--lift-accent);
          background: rgba(187,63,23,.07);
          color: var(--lift-ink) !important;
        }
        .lift-callout.model-transfer strong {
          color: var(--lift-ink) !important;
        }
        .lift-callout.model-transfer code {
          color: var(--lift-accent) !important;
          background: transparent;
          font-weight: 600;
        }
        .lift-callout.network-note {
          border-left-color: var(--lift-accent);
          background: rgba(187,63,23,.07);
          color: var(--lift-ink) !important;
        }
        .lift-callout.network-note strong {
          color: var(--lift-ink) !important;
        }
        .lift-equation {
          padding: 13px 14px;
          background: var(--lift-bg);
          border: 1px solid var(--lift-border);
          border-radius: 6px;
          margin-bottom: 9px;
          overflow-x: auto;
        }

        /* ================================================================
           MODEL TAB — static model architecture
           ================================================================ */
        .model-hero {
          display: grid;
          grid-template-columns: minmax(0, .82fr) minmax(560px, 1.18fr);
          gap: 16px;
          margin-bottom: 16px;
        }
        .model-hero-copy {
          background: var(--lift-ink);
          border-radius: 9px;
          padding: 30px;
          min-width: 0;
          color: var(--lift-bg);
        }
        .model-hero-copy .lift-section-kicker {
          color: #b9c9c0;
        }
        .model-hero-title {
          font-family: "Fraunces", Georgia, serif;
          font-size: 31px;
          line-height: 1.08;
          letter-spacing: -.025em;
          color: #f1e9da;
          margin: 0 0 11px;
        }
        .model-hero-text {
          margin: 0;
          color: #d6ded9;
          font-size: 12.5px;
          line-height: 1.72;
        }
        .model-hero-tags {
          display: flex;
          flex-wrap: wrap;
          gap: 7px;
          margin-top: 18px;
        }
        .model-hero-tag {
          display: inline-flex;
          align-items: center;
          gap: 6px;
          padding: 6px 9px;
          border-radius: 999px;
          border: 1px solid rgba(241,233,218,.15);
          background: rgba(255,255,255,.045);
          color: #dfe6e2;
          font-size: 8px;
          text-transform: uppercase;
          letter-spacing: .11em;
          font-weight: 700;
        }
        .model-tag-dot {
          width: 6px;
          height: 6px;
          border-radius: 50%;
          background: var(--lift-green);
        }
        .model-tag-dot.orange { background: var(--lift-warm); }
        .model-tag-dot.teal { background: var(--lift-teal); }

        .model-architecture {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 9px;
          padding: 22px;
          min-width: 0;
        }
        .model-architecture-head {
          display: flex;
          align-items: flex-start;
          justify-content: space-between;
          gap: 14px;
          margin-bottom: 15px;
        }
        .model-architecture-title {
          font-family: "Fraunces", Georgia, serif;
          color: var(--lift-ink);
          font-size: 20px;
          line-height: 1.15;
          margin: 0 0 4px;
        }
        .model-architecture-sub {
          margin: 0;
          color: var(--lift-faint);
          font-size: 10.5px;
          line-height: 1.55;
        }
        .model-architecture-chip {
          flex: 0 0 auto;
          padding: 6px 8px;
          border-radius: 999px;
          background: rgba(104,148,164,.09);
          border: 1px solid rgba(104,148,164,.24);
          color: var(--lift-ink);
          font-size: 7.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .11em;
          white-space: nowrap;
        }

        .model-pipeline {
          display: grid;
          grid-template-columns: minmax(135px,1fr) 34px minmax(135px,1fr) 34px minmax(135px,1fr) 34px minmax(135px,1fr);
          align-items: stretch;
          gap: 0;
          margin-top: 4px;
        }
        .model-stage {
          position: relative;
          border: 1px solid var(--lift-border);
          border-radius: 8px;
          padding: 14px 14px 13px;
          background: #fbf8f1;
          min-width: 0;
        }
        .model-stage.supplied {
          border-top: 3px solid var(--lift-green);
        }
        .model-stage.derived {
          border-top: 3px solid var(--lift-teal);
        }
        .model-stage.standard {
          border-top: 3px solid var(--lift-warm);
        }
        .model-stage.network {
          border-top: 3px solid var(--lift-accent);
        }
        .model-stage-step {
          color: var(--lift-faint);
          font-size: 7.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .13em;
          margin-bottom: 5px;
        }
        .model-stage-title {
          font-family: "Fraunces", Georgia, serif;
          color: var(--lift-ink);
          font-size: 16px;
          line-height: 1.15;
          margin-bottom: 7px;
        }
        .model-stage-eq {
          color: var(--lift-accent);
          font-size: 9px;
          font-weight: 700;
          line-height: 1.45;
          margin-bottom: 6px;
        }
        .model-stage-copy {
          color: var(--lift-faint);
          font-size: 9px;
          line-height: 1.45;
        }
        .model-pipeline-arrow {
          display: flex;
          align-items: center;
          justify-content: center;
          color: var(--lift-edge);
          font-family: "Fraunces", Georgia, serif;
          font-size: 23px;
        }

        .model-boundary {
          display: grid;
          grid-template-columns: 1fr 1fr;
          gap: 10px;
          margin-top: 13px;
        }
        .model-boundary-box {
          border-radius: 7px;
          padding: 11px 12px;
          font-size: 9.3px;
          line-height: 1.5;
        }
        .model-boundary-box.research {
          background: rgba(126,185,151,.09);
          border-left: 3px solid var(--lift-green);
          color: var(--lift-ink);
        }
        .model-boundary-box.standard {
          background: rgba(224,101,46,.07);
          border-left: 3px solid var(--lift-warm);
          color: var(--lift-ink);
        }
        .model-boundary-label {
          display: block;
          font-size: 7.5px;
          text-transform: uppercase;
          letter-spacing: .12em;
          color: var(--lift-faint);
          font-weight: 700;
          margin-bottom: 3px;
        }

        .model-equation-grid {
          display: grid;
          grid-template-columns: minmax(0,1fr) minmax(0,1fr);
          gap: 16px;
        }
        .model-equation-panel {
          background: var(--lift-white);
          border: 1px solid var(--lift-border);
          border-radius: 9px;
          padding: 22px;
          min-width: 0;
        }
        .model-panel-head {
          display: flex;
          justify-content: space-between;
          align-items: flex-start;
          gap: 14px;
          margin-bottom: 16px;
        }
        .model-origin-chip {
          flex: 0 0 auto;
          display: inline-flex;
          align-items: center;
          gap: 6px;
          padding: 6px 8px;
          border-radius: 999px;
          font-size: 7.5px;
          font-weight: 700;
          text-transform: uppercase;
          letter-spacing: .10em;
          white-space: nowrap;
        }
        .model-origin-chip.supplied {
          color: #285444;
          background: rgba(126,185,151,.13);
          border: 1px solid rgba(126,185,151,.32);
        }
        .model-origin-chip.standard {
          color: #854329;
          background: rgba(224,101,46,.09);
          border: 1px solid rgba(224,101,46,.25);
        }
        .model-origin-dot {
          width: 6px;
          height: 6px;
          border-radius: 50%;
          background: currentColor;
        }

        .model-eq-card {
          display: grid;
          grid-template-columns: 34px minmax(0,1fr);
          gap: 10px;
          align-items: center;
          padding: 12px 13px;
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          background: #fbf8f1;
          margin-bottom: 9px;
        }
        .model-eq-index {
          width: 30px;
          height: 30px;
          border-radius: 50%;
          display: flex;
          align-items: center;
          justify-content: center;
          background: var(--lift-ink);
          color: var(--lift-bg);
          font-family: "Fraunces", Georgia, serif;
          font-size: 12px;
        }
        .model-eq-card .lift-equation {
          margin: 0;
          padding: 4px 0;
          border: 0;
          background: transparent;
          border-radius: 0;
        }
        .model-eq-desc {
          color: var(--lift-faint);
          font-size: 9.5px;
          line-height: 1.45;
          margin-top: -1px;
        }

        .model-derived {
          margin-top: 15px;
          padding: 16px 17px;
          border-radius: 8px;
          background: var(--lift-ink);
          border: 1px solid #20382e;
        }
        .model-derived .lift-section-kicker {
          color: #aebeb5;
        }
        .model-derived-title {
          font-family: "Fraunces", Georgia, serif;
          color: #f1e9da;
          font-size: 17px;
          margin: 0 0 8px;
        }
        .model-derived p {
          color: #f1e9da !important;
          margin: 5px 0 !important;
          font-size: 11px;
        }
        .model-derived .MathJax,
        .model-derived mjx-container {
          color: #f1e9da !important;
        }

        .model-standard-equations {
          padding: 14px 15px 5px;
          border-radius: 8px;
          background: var(--lift-bg);
          border: 1px solid var(--lift-border);
          margin-bottom: 12px;
        }
        .model-standard-equations .lift-equation {
          background: var(--lift-white);
        }
        .model-research-note {
          margin-top: 12px;
          padding: 13px 14px;
          border-radius: 7px;
          border: 1px dashed #ccbca8;
          color: var(--lift-soft);
          background: #fbf8f1;
          font-size: 10.5px;
          line-height: 1.6;
        }

        @media (max-width: 1180px) {
          .model-hero {
            grid-template-columns: 1fr;
          }
        }
        @media (max-width: 900px) {
          .model-pipeline {
            grid-template-columns: 1fr;
            gap: 8px;
          }
          .model-pipeline-arrow {
            transform: rotate(90deg);
            height: 18px;
          }
          .model-equation-grid {
            grid-template-columns: 1fr;
          }
        }
        @media (max-width: 640px) {
          .model-hero-copy {
            padding: 22px;
          }
          .model-hero-title {
            font-size: 26px;
          }
          .model-architecture-head,
          .model-panel-head {
            flex-direction: column;
          }
          .model-boundary {
            grid-template-columns: 1fr;
          }
        }

        /* Plot containers */
        .lift-plot { min-height: 320px; }
        .lift-large-plot { min-height: 420px; }
        .lift-caption {
          text-align: center;
          margin-top: 7px;
          color: var(--lift-edge);
          font-size: 9px;
          letter-spacing: .2em;
          text-transform: uppercase;
        }

        /* Network scrubber */
        .lift-scrubber .form-group { margin-bottom: 0; }
        .lift-readout {
          padding: 14px;
          background: var(--lift-bg);
          border: 1px solid var(--lift-border);
          border-radius: 7px;
          font-size: 12px;
          line-height: 1.8;
          color: var(--lift-soft);
        }

        /* Hide shinydashboard box styling if any output inherits it. */
        .box { box-shadow: none !important; border-radius: 8px !important; border: 1px solid var(--lift-border) !important; }
        .box-header { background: transparent !important; border-bottom: 0 !important; }
        .box-title { font-family: "Fraunces", Georgia, serif !important; font-weight: 500 !important; }

        /* Large desktop screens get more breathing room inside the expanded
           canvas rather than unused space outside it. */
        @media (min-width: 1500px) {
          .lift-shell {
            padding-left: 30px;
            padding-right: 30px;
          }
          .lift-card {
            padding: 22px;
          }
        }

        /* Responsive */
        @media (max-width: 900px) {
          .lift-hero, .lift-grid-2, .lift-grid-3, .traffix-hero-layout,
          .setup-parameter-grid, .setup-summary, .network-top-stage, .network-guidance { grid-template-columns: 1fr; }
          .lift-form-grid { grid-template-columns: 1fr; }
          .setup-derived-grid { grid-template-columns: 1fr; }
          .lift-title { font-size: 38px; }
        }
        @media (max-width: 640px) {
          .lift-shell {
            width: 100%;
            max-width: none;
            padding: 18px 8px;
          }
          .lift-header-top { flex-direction: column; gap: 4px; }
          .lift-title { font-size: 34px; }
          .lift-nav-link { padding: 8px 10px; }
          .lift-run-wrap { flex-direction: column; align-items: stretch; }
          .setup-intro { align-items: flex-start; flex-direction: column; }
        }
      ')),

      # Keep the custom top-navigation highlight and Shiny tab state in sync.
      tags$script(HTML("
        $(document).on('shiny:connected', function(){
          function syncLiftNav(tabName){
            if(!tabName){
              tabName = $('.sidebar-menu .active a').attr('data-value') ||
                        $('.tab-content .tab-pane.active').attr('id');
              if(tabName){ tabName = tabName.replace('shiny-tab-', ''); }
              tabName = tabName || 'home';
            }
            $('.lift-nav-link').removeClass('active');
            $('.lift-nav-link[data-tab=\"' + tabName + '\"]').addClass('active');
          }

          syncLiftNav();

          // Fires whenever the real Shiny tab input changes.
          $(document).on('shiny:inputchanged', function(event){
            if(event.name === 'tabs'){
              syncLiftNav(event.value);
            }
          });

          // Backup for Bootstrap/shinydashboard tab transitions.
          // visNetwork can calculate a zero-size canvas when its tab was hidden;
          // trigger a browser resize as soon as the Network tab becomes visible.
          $(document).on('shown.bs.tab', function(e){
            setTimeout(syncLiftNav, 10);
            var href = $(e.target).attr('href') || '';
            if(href.indexOf('shiny-tab-network') !== -1){
              setTimeout(function(){ $(window).trigger('resize'); }, 120);
              setTimeout(function(){ $(window).trigger('resize'); }, 450);
            }
          });
        });

        // ---- Fast map animation: restyle existing layers instead of redrawing ----
        $(function(){
          var heads = {};
          function arr(x){ return (x === null || x === undefined) ? [] : [].concat(x); }
          function getMap(){
            var w = window.HTMLWidgets && HTMLWidgets.find('#net_map');
            return (w && w.getMap) ? w.getMap() : null;
          }
          function hook(l){
            if(l.__tfx) return;
            l.__tfx = true;
            l.on('mouseover', function(){
              l.__hover = true;
              l.setStyle({color:'#182d23', weight:11, opacity:1});
              if(l.bringToFront) l.bringToFront();
            });
            l.on('mouseout', function(){
              l.__hover = false;
              l.setStyle({color:l.__c, weight:l.__w, opacity:0.97});
            });
          }
          Shiny.addCustomMessageHandler('traffix_heads', function(m){
            heads = {};
            var ids = arr(m.ids), h = arr(m.heads);
            for(var i = 0; i < ids.length; i++){ heads[ids[i]] = h[i]; }
          });
          Shiny.addCustomMessageHandler('traffix_style', function(m){
            var map = getMap();
            if(!map || !map.layerManager) return;
            var lm = map.layerManager;
            var ids = arr(m.ids), col = arr(m.color), wt = arr(m.weight);
            var dn = arr(m.dens), sp = arr(m.speed), fl = arr(m.flow);
            for(var i = 0; i < ids.length; i++){
              var l = lm.getLayer('shape', ids[i]);
              if(!l) continue;
              hook(l);
              l.__c = col[i]; l.__w = wt[i];
              if(!l.__hover) l.setStyle({color:col[i], weight:wt[i]});
              if(heads[ids[i]] !== undefined && l.setTooltipContent){
                l.setTooltipContent(heads[ids[i]] + '<br>Density: ' + dn[i] + '% of jam' +
                  '<br>Speed: ' + sp[i] + ' km/h' + '<br>FD flow potential: ' + fl[i] + ' veh/h');
              }
            }
            var nid = arr(m.node_ids), nf = arr(m.node_fill), nr = arr(m.node_radius), hr = arr(m.halo_radius);
            for(var k = 0; k < nid.length; k++){
              var n = lm.getLayer('marker', nid[k]);
              if(n){ n.setStyle({fillColor:nf[k]}); n.setRadius(nr[k]); }
              var h = lm.getLayer('marker', 'halo_' + (k + 1));
              if(h){ h.setStyle({fillColor:nf[k]}); h.setRadius(hr[k]); }
            }
          });
        });
      "))
    ),

    div(class = "lift-shell",

      # Header
      div(class = "lift-header",
        div(class = "lift-header-top",
          span(class = "lift-eyebrow", "BSc Honours — Mathematical Statistics | Traffic Simulation"),
          span(class = "lift-eyebrow", "TraffiX Research Platform")
        ),
        h1(class = "lift-title", HTML("TraffiX<span>.</span>")),
        p(class = "lift-subtitle", "Link-level Interrupted Flow Traffic Dynamics on Spatial Linear Networks")
      ),

      # Navigation
      # These controls send the selected tab to Shiny so the page and the
      # highlighted navigation item always stay synchronized.
      tags$nav(class = "lift-nav", role = "navigation",
        tags$a(class = "lift-nav-link active", href = "#", `data-tab` = "home",
               onclick = "Shiny.setInputValue('lift_nav', 'home', {priority: 'event'}); return false;",
               icon("house"), "Overview"),
        tags$a(class = "lift-nav-link", href = "#", `data-tab` = "model",
               onclick = "Shiny.setInputValue('lift_nav', 'model', {priority: 'event'}); return false;",
               icon("square-root-variable"), "Model"),
        tags$a(class = "lift-nav-link", href = "#", `data-tab` = "setup",
               onclick = "Shiny.setInputValue('lift_nav', 'setup', {priority: 'event'}); return false;",
               icon("sliders"), "Simulation Setup"),
        tags$a(class = "lift-nav-link", href = "#", `data-tab` = "network",
               onclick = "Shiny.setInputValue('lift_nav', 'network', {priority: 'event'}); return false;",
               icon("share-nodes"), "Network"),
        tags$a(class = "lift-nav-link", href = "#", `data-tab` = "results",
               onclick = "Shiny.setInputValue('lift_nav', 'results', {priority: 'event'}); return false;",
               icon("chart-area"), "Results"),
        tags$a(class = "lift-nav-link", href = "#", `data-tab` = "about",
               onclick = "Shiny.setInputValue('lift_nav', 'about', {priority: 'event'}); return false;",
               icon("circle-info"), "About")
      ),


      tabItems(

        # ======================================================
        # HOME / OVERVIEW
        # ======================================================
        tabItem(
          tabName = "home",

          div(class = "lift-hero",
            div(class = "lift-hero-main",
              div(class = "traffix-hero-layout",
                div(class = "lift-hero-copy",
                  p(class = "lift-section-kicker", "Research simulation platform"),
                  h2("Traffic simulation built around interrupted flow."),
                  p("TraffiX represents traffic movement on spatial linear networks using event-based link transitions and a continuously updated description of congestion and unused road capacity. Explore how spacing, demand and interruptions reshape network performance."),
                  div(class = "lift-callout teal",
                    strong("Research focus: "),
                    "traffic dynamics, spatial linear networks, spillback and interrupted flow."
                  )
                ),
                div(class = "traffix-traffic-scene",
                  div(class = "traffix-scene-label", "Live network illustration"),
                  div(class = "traffix-scene-status",
                    div(class = "traffix-scene-status-dot"),
                    "FLOW ACTIVE"
                  ),
                  div(class = "traffix-node n1"),
                  div(class = "traffix-node n2"),
                  div(class = "traffix-node n3"),
                  div(class = "traffix-node n4"),
                  div(class = "traffix-road",
                    div(class = "traffix-lane-markings"),
                    div(class = "traffix-road-glow")
                  ),
                  div(class = "traffix-light",
                    span(class = "traffix-bulb red"),
                    span(class = "traffix-bulb amber"),
                    span(class = "traffix-bulb green")
                  ),
                  div(class = "traffix-queue",
                    div(class = "traffix-queue-dot"),
                    "interruption"
                  ),
                  div(class = "traffix-car car-light c1", div(class = "body"), div(class = "cabin"), div(class = "wheel w1"), div(class = "wheel w2")),
                  div(class = "traffix-car car-teal c2", div(class = "body"), div(class = "cabin"), div(class = "wheel w1"), div(class = "wheel w2")),
                  div(class = "traffix-car car-orange c3", div(class = "body"), div(class = "cabin"), div(class = "wheel w1"), div(class = "wheel w2")),
                  div(class = "traffix-car car-green c4", div(class = "body"), div(class = "cabin"), div(class = "wheel w1"), div(class = "wheel w2")),
                  div(class = "traffix-car car-light c5", div(class = "body"), div(class = "cabin"), div(class = "wheel w1"), div(class = "wheel w2")),
                  div(class = "traffix-flowline",
                    span("FREE FLOW"),
                    span("QUEUE / SPILLBACK"),
                    span(class = "traffix-flow-arrow", "→")
                  )
                )
              )
            ),
            div(class = "lift-hero-side",
              p(class = "lift-section-kicker", "Workflow"),
              strong("1. Adjust → 2. Recalculate → 3. Explore"),
              p("Adjust the four live traffic parameters, let TraffiX recalculate automatically, then investigate the network state and performance measures over time."),
              div(style = "height:12px;"),
              p(class = "lift-section-kicker", "Model transparency"),
              strong("Equations first. Assumptions visible."),
              p("The Model section clearly separates the supplied TraffiX equations from standard traffic-flow components used to complete the simulator.")
            )
          ),

          div(class = "lift-kpis",
            div(class = "lift-kpi",
              div(class = "lift-kpi-label", "Core relation"),
              div(class = "lift-kpi-value", HTML("t<sub>event</sub> = max(exit, entry)")),
              div(class = "lift-kpi-sub", "Per-link transition timing")
            ),
            div(class = "lift-kpi teal",
              div(class = "lift-kpi-label", "Vehicle spacing"),
              div(class = "lift-kpi-value", HTML("l<sup>eff</sup> = l<sub>veh</sub> + g")),
              div(class = "lift-kpi-sub", "Effective occupied length")
            ),
            div(class = "lift-kpi green",
              div(class = "lift-kpi-label", "Space speed"),
              div(class = "lift-kpi-value", HTML("V<sup>space</sup> = l<sup>eff</sup> / r")),
              div(class = "lift-kpi-sub", "Derived free-flow speed")
            ),
            div(class = "lift-kpi warm",
              div(class = "lift-kpi-label", "Network loading"),
              div(class = "lift-kpi-value", "CTM"),
              div(class = "lift-kpi-sub", "Cell Transmission implementation")
            )
          ),

          div(class = "lift-grid-2",
            div(class = "lift-card",
              p(class = "lift-section-kicker", "What this app does"),
              h2(class = "lift-card-title", "From equations to network behaviour"),
              p(class = "lift-card-subtitle", "The simulator connects vehicle spacing with traffic loading, junction interruptions and network performance."),
              tags$ul(style = "padding-left:18px; margin:0; color:var(--lift-soft); font-size:12px; line-height:1.9;",
                tags$li("Builds corridor, ring, grid and random directed network topologies."),
                tags$li("Derives free-flow speed, jam density and capacity from the parameterisation."),
                tags$li("Represents signals and node incidents as interruptions to flow."),
                tags$li("Tracks speed, vehicles, delay and throughput over simulation time.")
              )
            ),
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Recommended workflow"),
              h2(class = "lift-card-title", "Start with Simulation Setup"),
              p(class = "lift-card-subtitle", "The app is designed to be read from left to right: tune the four active parameters, then interpret the automatically updated outputs."),
              div(class = "lift-callout",
                strong("Step 01 — "), "Set vehicle length and minimum gap.", br(),
                strong("Step 02 — "), "Set time headway and backward wave speed.", br(),
                strong("Step 03 — "), "TraffiX recalculates automatically as the inputs change.", br(),
                strong("Step 04 — "), "Use Model to document exactly how the equations enter the simulation."
              )
            )
          )
        ),

        # ======================================================
        # SETUP
        # ======================================================
        tabItem(
          tabName = "setup",

          # Live model outputs first
          div(class = "lift-kpis",
            div(class = "lift-kpi",
              div(class = "lift-kpi-label", "Free-flow speed"),
              div(class = "lift-kpi-value", textOutput("home_speed", inline = TRUE)),
              div(class = "lift-kpi-sub", HTML("V<sub>f</sub> = l<sup>eff</sup> / r"))
            ),
            div(class = "lift-kpi teal",
              div(class = "lift-kpi-label", "Jam density"),
              div(class = "lift-kpi-value", textOutput("home_density", inline = TRUE)),
              div(class = "lift-kpi-sub", HTML("k<sub>jam</sub> = 1 / l<sup>eff</sup>"))
            ),
            div(class = "lift-kpi green",
              div(class = "lift-kpi-label", "Capacity"),
              div(class = "lift-kpi-value", textOutput("home_capacity", inline = TRUE)),
              div(class = "lift-kpi-sub", "Triangular traffic-flow capacity")
            )
          ),

          div(class = "setup-intro",
            div(class = "setup-intro-copy",
              p(class = "lift-section-kicker", "Live parameterisation"),
              h2(class = "lift-card-title", "Simulation Setup"),
              p(class = "lift-card-subtitle",
                "Tune the four parameters that directly drive the current TraffiX implementation. ",
                "Every change is applied automatically to the network and results — there is no separate run step."
              )
            ),
            div(class = "setup-live-badge",
              span(class = "setup-live-dot"),
              "Auto recalculation"
            )
          ),

          div(class = "setup-parameter-grid",

            div(class = "setup-parameter-card geometry",
              p(class = "lift-section-kicker", "Vehicle geometry"),
              h3(class = "lift-card-title", "Occupied road space"),
              p(class = "lift-card-subtitle",
                "Vehicle length and minimum gap combine to determine the effective spacing used by the model."
              ),

              div(class = "setup-control-block",
                div(class = "lift-control",
                  sliderInput(
                    "l_veh",
                    HTML("Vehicle length, l<sub>veh</sub> (m)"),
                    min = 3, max = 8, value = 4.5, step = 0.1
                  )
                ),
                p(class = "setup-param-help",
                  "Physical vehicle length. Increasing it raises effective occupied road space."
                )
              ),

              div(class = "setup-control-block",
                div(class = "lift-control",
                  sliderInput(
                    "g_gap",
                    HTML("Minimum gap, g (m)"),
                    min = 0.5, max = 5, value = 2, step = 0.1
                  )
                ),
                p(class = "setup-param-help",
                  "Minimum spacing between successive vehicles in the link-level representation."
                )
              )
            ),

            div(class = "setup-parameter-card response",
              p(class = "lift-section-kicker", "Traffic response"),
              h3(class = "lift-card-title", "Speed & congestion propagation"),
              p(class = "lift-card-subtitle",
                "Headway determines free-flow speed, while the wave factor controls how quickly congestion propagates backward."
              ),

              div(class = "setup-control-block",
                div(class = "lift-control",
                  sliderInput(
                    "r_headway",
                    HTML("Time headway, r (s)"),
                    min = 0.5, max = 3, value = 1.2, step = 0.1
                  )
                ),
                p(class = "setup-param-help",
                  "Time separation used in Vspace = leff / r. Lower headway produces a higher free-flow speed."
                )
              ),

              div(class = "setup-control-block",
                div(class = "lift-control",
                  sliderInput(
                    "wave_factor",
                    HTML("Backward wave speed, w / V<sub>f</sub>"),
                    min = 0.15, max = 1, value = 0.4, step = 0.05
                  )
                ),
                p(class = "setup-param-help",
                  "Fraction of free-flow speed used for the backward-moving congestion wave."
                )
              )
            )
          ),

          div(class = "setup-summary",
            div(class = "setup-derived",
              p(class = "lift-section-kicker", "Current parameterisation"),
              h3(class = "setup-derived-title", "What your four inputs imply"),
              uiOutput("setup_live_summary")
            ),

            div(class = "setup-assumptions",
              p(class = "lift-section-kicker", "Fixed simulation context"),
              h3(class = "lift-card-title", "Background settings"),
              p(class = "lift-card-subtitle",
                "These are held constant so the Setup page focuses only on the four parameters that currently drive your research model."
              ),

              div(class = "setup-assumption-row",
                span(class = "setup-assumption-name", "Network"),
                span(class = "setup-assumption-value", "Lynnwood Road corridor · 8 nodes")
              ),
              div(class = "setup-assumption-row",
                span(class = "setup-assumption-name", "Demand"),
                span(class = "setup-assumption-value", "900 veh/h")
              ),
              div(class = "setup-assumption-row",
                span(class = "setup-assumption-name", "Simulation horizon"),
                span(class = "setup-assumption-value", "10 min")
              ),
              div(class = "setup-assumption-row",
                span(class = "setup-assumption-name", "Signal regime"),
                span(class = "setup-assumption-value", "60 s cycle · 50% green")
              ),

              div(class = "setup-auto-note",
                strong("Live model: "),
                "release a slider and TraffiX automatically recalculates the simulation, network state and Results tab."
              )
            )
          )
        ),

        # ======================================================
        # NETWORK
        # ======================================================
        tabItem(
          tabName = "network",

          div(class = "network-method-card",
            div(class = "network-method-head",
              div(class = "network-method-head-copy",
                p(class = "lift-section-kicker", "Network mechanics"),
                h2(class = "lift-card-title", "How traffic moves through the TraffiX corridor"),
                p(class = "lift-card-subtitle",
                  "A simplified linear-network schematic inspired by the teaching-network approach: ",
                  "traffic enters at the source, moves link by link through junctions, can queue around an interruption, ",
                  "and eventually exits at the sink. This diagram is explanatory rather than interactive."
                )
              ),
              div(class = "network-method-badge",
                span(class = "network-method-badge-dot"),
                "Conceptual corridor schematic"
              )
            ),

            div(class = "network-method-stage",
              div(class = "network-method-stage-inner",
                div(class = "network-method-flowbar",
                  div(class = "network-method-flowlabel",
                    div(class = "network-method-flowline forward"),
                    "Downstream vehicle flow"
                  ),
                  div(class = "network-method-flowlabel",
                    "Congestion propagation",
                    div(class = "network-method-flowline backward")
                  )
                ),

                div(class = "network-method-track",
                  div(class = "network-method-node source",
                    div(class = "network-method-node-circle", "N1"),
                    div(class = "network-method-node-name", "Source"),
                    div(class = "network-method-node-role", "Demand enters")
                  ),
                  div(class = "network-method-link",
                    span(class = "network-method-link-label", "L1")
                  ),

                  div(class = "network-method-node junction",
                    div(class = "network-method-node-circle", "N2"),
                    div(class = "network-method-node-name", "Junction"),
                    div(class = "network-method-node-role", "Link transfer")
                  ),
                  div(class = "network-method-link",
                    span(class = "network-method-link-label", "L2")
                  ),

                  div(class = "network-method-node junction",
                    div(class = "network-method-node-circle", "N3"),
                    div(class = "network-method-node-name", "Junction"),
                    div(class = "network-method-node-role", "Link transfer")
                  ),
                  div(class = "network-method-link moderate",
                    span(class = "network-method-link-label", "L3")
                  ),

                  div(class = "network-method-node junction",
                    div(class = "network-method-node-circle", "N4"),
                    div(class = "network-method-node-name", "Junction"),
                    div(class = "network-method-node-role", "Queue begins")
                  ),
                  div(class = "network-method-link congested",
                    span(class = "network-method-link-label", "L4")
                  ),

                  div(class = "network-method-node signal",
                    div(class = "network-method-node-circle", "N5"),
                    div(class = "network-method-node-name", "Interrupted"),
                    div(class = "network-method-node-role", "Signal / restriction")
                  ),
                  div(class = "network-method-link recovery",
                    span(class = "network-method-link-label", "L5")
                  ),

                  div(class = "network-method-node junction",
                    div(class = "network-method-node-circle", "N6"),
                    div(class = "network-method-node-name", "Junction"),
                    div(class = "network-method-node-role", "Queue releases")
                  ),
                  div(class = "network-method-link",
                    span(class = "network-method-link-label", "L6")
                  ),

                  div(class = "network-method-node junction",
                    div(class = "network-method-node-circle", "N7"),
                    div(class = "network-method-node-name", "Junction"),
                    div(class = "network-method-node-role", "Downstream")
                  ),
                  div(class = "network-method-link",
                    span(class = "network-method-link-label", "L7")
                  ),

                  div(class = "network-method-node sink",
                    div(class = "network-method-node-circle", "N8"),
                    div(class = "network-method-node-name", "Sink"),
                    div(class = "network-method-node-role", "Vehicles exit")
                  )
                ),

                div(class = "network-method-wave",
                  "← backward-moving congestion wave / spillback"
                ),

                div(class = "network-method-legend",
                  div(class = "network-method-legend-item",
                    span(class = "network-method-legend-dot"),
                    "Normal junction"
                  ),
                  div(class = "network-method-legend-item",
                    span(class = "network-method-legend-dot orange"),
                    "Interruption point"
                  ),
                  div(class = "network-method-legend-item",
                    span(class = "network-method-legend-line"),
                    "Link loading / congestion"
                  ),
                  div(class = "network-method-legend-item",
                    span(class = "network-method-legend-dot purple"),
                    "Sink"
                  )
                )
              )
            ),

            div(class = "network-method-steps",
              div(class = "network-method-step",
                div(class = "network-method-step-number", "1"),
                div(class = "network-method-step-title", "Demand enters"),
                div(class = "network-method-step-copy",
                  "Vehicles enter through the source node and begin loading the first road link."
                )
              ),
              div(class = "network-method-step",
                div(class = "network-method-step-number", "2"),
                div(class = "network-method-step-title", "Links store traffic"),
                div(class = "network-method-step-copy",
                  "Each link carries a density state and passes flow downstream subject to available capacity."
                )
              ),
              div(class = "network-method-step",
                div(class = "network-method-step-number", "3"),
                div(class = "network-method-step-title", "Interruptions create queues"),
                div(class = "network-method-step-copy",
                  "A restricted junction reduces transfer capacity and congestion can spill backward into upstream links."
                )
              ),
              div(class = "network-method-step",
                div(class = "network-method-step-number", "4"),
                div(class = "network-method-step-title", "Traffic clears"),
                div(class = "network-method-step-copy",
                  "Once downstream receiving capacity is available, the queue dissipates and vehicles leave through the sink."
                )
              )
            )
          ),

          div(class = "corridor-playback-card",

            div(class = "corridor-playback-intro",
              p(class = "lift-section-kicker", "Corridor playback"),
              h3(class = "corridor-playback-title", "Control the Lynnwood Road simulation"),
              p(class = "corridor-playback-copy",
                "The Pretoria Study Corridor below is now the primary live network view. ",
                "Use these controls to change what the road colours represent and to move through the simulation."
              ),
              div(class = "corridor-playback-note",
                span(class = "corridor-playback-dot"),
                "Controls update the map directly"
              )
            ),

            div(class = "corridor-playback-block",
              div(class = "corridor-playback-label", "Road-link colouring"),
              selectInput(
                "network_metric", NULL,
                choices = c(
                  "Density (% of jam)" = "density",
                  "Speed (km/h)" = "speed",
                  "FD flow potential (veh/h)" = "flow"
                ),
                selected = "density",
                width = "100%"
              ),
              p(class = "setup-param-help",
                "Colours use fixed model-based scales, so the same colour has the same meaning at every animation step."
              )
            ),

            div(class = "corridor-playback-block",
              div(class = "corridor-playback-label", "Simulation time"),
              div(class = "corridor-playback-time",
                div(class = "corridor-playback-slider",
                  div(class = "lift-control lift-scrubber", uiOutput("time_slider_ui"))
                ),
                div(class = "corridor-playback-toggle",
                  checkboxInput("animate", "Animate Pretoria corridor", value = FALSE)
                )
              ),
              div(class = "corridor-playback-readout",
                div(class = "lift-readout", htmlOutput("phase_readout"))
              )
            )
          ),

          div(class = "lift-map-layout",
            div(class = "lift-card", style = "min-width:0;",
              p(class = "lift-section-kicker", "Pretoria study corridor"),
              h2(class = "lift-card-title", "Lynnwood Road Traffic Exposure Map"),
              p(class = "lift-card-subtitle", "A real Pretoria basemap with the displayed corridor derived directly from OpenStreetMap geometry for Lynnwood Road. Every simulated node and coloured link is sampled from that one centreline. Hover over the corridor to inspect the live traffic state."),
              div(class = "lift-map-frame",
                leafletOutput("net_map", height = "560px")
              ),
              div(class = "lift-map-footer", paste0("Pretoria · Gauteng — Lynnwood Road study corridor · ", LYNNWOOD_ROUTE_SOURCE))
            ),
            div(class = "lift-map-side",
              div(class = "lift-card",
                p(class = "lift-section-kicker", "Map inspector"),
                h2(class = "lift-card-title", "Live Corridor State"),
                p(class = "lift-card-subtitle", "Hover over a coloured road link or node to update this inspector instantly. On touch devices, tap the element instead. The values continue to update as you scrub through simulation time."),
                uiOutput("map_selection")
              ),
              div(class = "lift-card",
                p(class = "lift-section-kicker", "Map encoding"),
                h2(class = "lift-card-title", "How to read the map"),
                div(class = "lift-map-key-row",
                  div(class = "lift-map-key-line"),
                  div(strong("Link colour"), tags$br(), "Uses a fixed absolute scale for the selected density / speed / FD-flow metric, so colours remain comparable through time.")
                ),
                div(class = "lift-map-key-row",
                  div(class = "lift-map-dot", style = "background:#2ECC71;margin-top:4px;"),
                  div(strong("Junction state"), tags$br(), "Green and red junction markers reflect the current signal phase when signalisation is enabled.")
                ),
                div(class = "lift-map-key-row",
                  div(class = "lift-map-dot", style = "background:#bb3f17;margin-top:4px;"),
                  div(strong("Circle size"), tags$br(), "Larger node halos indicate greater congestion on links touching that node.")
                ),
                div(class = "lift-callout network-note",
                  strong("Study-area note: "), "the basemap is real. The displayed corridor is reconstructed from OpenStreetMap ways explicitly named Lynnwood Road, and every node and coloured link is sampled from that same centreline. The node positions are for research visualisation and are not measured GPS traffic sensors."
                )
              )
            )
          )
        ),

        # ======================================================
        # RESULTS
        # ======================================================
        tabItem(
          tabName = "results",
          div(class = "lift-card",
            p(class = "lift-section-kicker", "Link-level diagnostics"),
            h2(class = "lift-card-title", "Per-Link Summary"),
            p(class = "lift-card-subtitle", "Average and maximum density, speed and physical link length."),
            div(
              style = "display:flex;gap:8px;flex-wrap:wrap;margin:0 0 16px 0;",
              downloadButton("download_time_series", "Download network time series", class = "btn btn-default"),
              downloadButton("download_link_time_series", "Download link time series", class = "btn btn-default"),
              downloadButton("download_link_summary", "Download link summary", class = "btn btn-default"),
              downloadButton("download_cell_states", "Download detailed cell states", class = "btn btn-default"),
              downloadButton("download_parameters", "Download parameters", class = "btn btn-default")
            ),
            DTOutput("link_table")
          ),
          div(class = "lift-grid-2",
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Network performance"),
              h2(class = "lift-card-title", "Average Speed"),
              p(class = "lift-card-subtitle", "Network-average speed over simulation time."),
              plotlyOutput("speed_t_plot", height = "320px")
            ),
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Network loading"),
              h2(class = "lift-card-title", "Vehicles in Network"),
              p(class = "lift-card-subtitle", "Number of vehicles occupying the simulated links through time."),
              plotlyOutput("veh_t_plot", height = "320px")
            )
          ),
          div(class = "lift-grid-2",
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Congestion impact"),
              h2(class = "lift-card-title", "Cumulative Delay"),
              p(class = "lift-card-subtitle", "Accumulated vehicle-hours of delay relative to the derived free-flow speed."),
              plotlyOutput("delay_t_plot", height = "320px")
            ),
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Network output"),
              h2(class = "lift-card-title", "Cumulative Throughput"),
              p(class = "lift-card-subtitle", "Vehicles successfully exiting through sink nodes."),
              plotlyOutput("throughput_t_plot", height = "320px")
            )
          )
        ),

        # ======================================================
        # MODEL
        # ======================================================
        tabItem(
          tabName = "model",

          div(class = "model-hero",
            div(class = "model-hero-copy",
              p(class = "lift-section-kicker", "Model architecture"),
              h2(class = "model-hero-title", "From vehicle spacing to network flow."),
              p(class = "model-hero-text",
                "TraffiX starts with the supplied link-level relations for event timing, occupied road space and space-mean speed. ",
                "Those quantities are then connected to a triangular fundamental diagram and Cell Transmission logic so that traffic can move, queue, spill back and clear across the corridor."
              ),
              div(class = "model-hero-tags",
                span(class = "model-hero-tag",
                  span(class = "model-tag-dot"),
                  "Supplied equations"
                ),
                span(class = "model-hero-tag",
                  span(class = "model-tag-dot teal"),
                  "Derived traffic state"
                ),
                span(class = "model-hero-tag",
                  span(class = "model-tag-dot orange"),
                  "Standard CTM components"
                )
              )
            ),

            div(class = "model-architecture",
              div(class = "model-architecture-head",
                div(
                  p(class = "lift-section-kicker", "Model flow"),
                  h3(class = "model-architecture-title", "How the pieces fit together"),
                  p(class = "model-architecture-sub",
                    "A static view of the modelling chain used by the current TraffiX implementation."
                  )
                ),
                div(class = "model-architecture-chip", "Research → implementation")
              ),

              div(class = "model-pipeline",
                div(class = "model-stage supplied",
                  div(class = "model-stage-step", "01 · Supplied"),
                  div(class = "model-stage-title", "Vehicle & event relations"),
                  div(class = "model-stage-eq", "tevent · leff · Vspace"),
                  div(class = "model-stage-copy",
                    "Defines transition timing, occupied vehicle length and space-mean speed."
                  )
                ),
                div(class = "model-pipeline-arrow", "→"),

                div(class = "model-stage derived",
                  div(class = "model-stage-step", "02 · Derived"),
                  div(class = "model-stage-title", "Traffic state parameters"),
                  div(class = "model-stage-eq", "vf · kjam · w · qmax"),
                  div(class = "model-stage-copy",
                    "Transforms the supplied spacing relations into free-flow speed, jam density and capacity."
                  )
                ),
                div(class = "model-pipeline-arrow", "→"),

                div(class = "model-stage standard",
                  div(class = "model-stage-step", "03 · Standard"),
                  div(class = "model-stage-title", "Fundamental diagram"),
                  div(class = "model-stage-eq", "q(k) · S(k) · R(k)"),
                  div(class = "model-stage-copy",
                    "Describes how much flow a cell can send and how much the next cell can receive."
                  )
                ),
                div(class = "model-pipeline-arrow", "→"),

                div(class = "model-stage network",
                  div(class = "model-stage-step", "04 · Network"),
                  div(class = "model-stage-title", "Cell Transmission Model"),
                  div(class = "model-stage-eq", "flow = min(S, R)"),
                  div(class = "model-stage-copy",
                    "Moves traffic through the corridor while preserving flow conservation and allowing spillback."
                  )
                )
              ),

              div(class = "model-boundary",
                div(class = "model-boundary-box research",
                  span(class = "model-boundary-label", "Research-defined"),
                  strong("Core TraffiX relations: "),
                  "event timing, effective occupied length and space-mean speed."
                ),
                div(class = "model-boundary-box standard",
                  span(class = "model-boundary-label", "Implementation layer"),
                  strong("Standard traffic-flow theory: "),
                  "triangular FD, sending/receiving functions and CTM network loading."
                )
              )
            )
          ),

          div(class = "model-equation-grid",

            div(class = "model-equation-panel",
              div(class = "model-panel-head",
                div(
                  p(class = "lift-section-kicker", "Research equations"),
                  h2(class = "lift-card-title", "Your TraffiX Equations"),
                  p(class = "lift-card-subtitle",
                    "These are the core relations supplied for the research model."
                  )
                ),
                div(class = "model-origin-chip supplied",
                  span(class = "model-origin-dot"),
                  "Supplied"
                )
              ),

              withMathJax(),

              div(class = "model-eq-card",
                div(class = "model-eq-index", "1"),
                div(
                  div(class = "lift-equation",
                    helpText("$$t_{\\mathrm{event}} = \\max\\!\\left(d_{N_i^{\\mathrm{out}}}^{\\mathrm{exit}},\\; s_{N_i^{\\mathrm{in}}}^{\\mathrm{entry}}\\right)$$")
                  ),
                  div(class = "model-eq-desc",
                    "Per-link transition timing: the event occurs when the binding exit/entry condition is satisfied."
                  )
                )
              ),

              div(class = "model-eq-card",
                div(class = "model-eq-index", "2"),
                div(
                  div(class = "lift-equation",
                    helpText("$$l^{\\mathrm{eff}} = l_{\\mathrm{veh}} + g$$")
                  ),
                  div(class = "model-eq-desc",
                    "Effective occupied length combines physical vehicle length with the minimum following gap."
                  )
                )
              ),

              div(class = "model-eq-card",
                div(class = "model-eq-index", "3"),
                div(
                  div(class = "lift-equation",
                    helpText("$$V^{\\mathrm{space}} = \\frac{l^{\\mathrm{eff}}}{r}$$")
                  ),
                  div(class = "model-eq-desc",
                    "Space-mean / free-flow speed follows from effective spacing divided by time headway."
                  )
                )
              ),

              div(class = "model-derived",
                p(class = "lift-section-kicker", "Current parameterisation"),
                h3(class = "model-derived-title", "Live values from Simulation Setup"),
                uiOutput("derived_eqns")
              )
            ),

            div(class = "model-equation-panel",
              div(class = "model-panel-head",
                div(
                  p(class = "lift-section-kicker", "Standard traffic-flow components"),
                  h2(class = "lift-card-title", "Filled-in Simulation Components"),
                  p(class = "lift-card-subtitle",
                    "These standard relationships complete the runnable simulator where the supplied equations do not specify a flow-density or conservation rule."
                  )
                ),
                div(class = "model-origin-chip standard",
                  span(class = "model-origin-dot"),
                  "Standard theory"
                )
              ),

              withMathJax(),

              div(class = "model-standard-equations",
                p(class = "lift-section-kicker", "Triangular fundamental diagram"),
                div(class = "lift-equation",
                  helpText("$$q(k) = \\min\\big(v_f k,\\; w\\,(k_{\\text{jam}}-k)\\big)$$")
                ),
                p(class = "model-eq-desc",
                  "The free-flow and congested branches meet at capacity."
                )
              ),

              div(class = "model-standard-equations",
                p(class = "lift-section-kicker", "Sending & receiving"),
                div(class = "lift-equation",
                  helpText("$$S(k) = \\min(v_f k,\\, q_{\\max}) \\qquad R(k) = \\min(q_{\\max},\\, w(k_{\\text{jam}}-k))$$")
                ),
                p(class = "model-eq-desc",
                  "Sending measures what the upstream cell can release; receiving measures what the downstream cell can accept."
                )
              ),

              div(class = "lift-callout model-transfer",
                strong("Transfer rule: "),
                code("flow = min(S_upstream, R_downstream)"),
                " is used as the conservation-law counterpart of the event-time max rule."
              ),

              div(class = "model-research-note",
                strong("Research boundary: "),
                "the triangular fundamental diagram, capacity equation and CTM merge/diverge logic are standard modelling components used to make the simulator operational. ",
                "If the final thesis specifies alternatives, those components can be replaced while retaining the surrounding TraffiX interface."
              )
            )
          )
        ),

        # ======================================================
        # ABOUT
        # ======================================================
        tabItem(
          tabName = "about",
          div(class = "lift-hero",
            div(class = "lift-hero-main",
              p(class = "lift-section-kicker", "Honours research project"),
              h2("LIFT — Link-level Interrupted Flow Traffic Dynamics"),
              p("This application provides an interactive environment for experimenting with traffic simulation on spatial linear networks. It is designed to connect the mathematical formulation with an observable, time-evolving network representation."),
              div(class = "lift-callout teal",
                strong("Purpose: "), "support model development, interpretation and communication during the Honours research project."
              )
            ),
            div(class = "lift-hero-side",
              p(class = "lift-section-kicker", "Scope"),
              strong("Topology → loading → interruption → performance"),
              p("The current research build focuses on the Lynnwood Road corridor with four live vehicle/traffic parameters, automatic network recalculation, density-aware visualisation and network-level KPIs."),
              div(style = "height:12px;"),
              p(class = "lift-section-kicker", "Model provenance"),
              strong("Transparent assumptions"),
              p("The Model page explicitly flags components that were filled in using standard traffic-flow theory rather than presenting them as original supplied equations.")
            )
          ),
          div(class = "lift-grid-2",
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Application structure"),
              h2(class = "lift-card-title", "What each section is for"),
              tags$ul(style = "padding-left:18px; margin:0; color:var(--lift-soft); font-size:12px; line-height:1.9;",
                tags$li(strong("Overview — "), "research context and workflow."),
                tags$li(strong("Simulation Setup — "), "four live model parameters with automatic recalculation."),
                tags$li(strong("Network — "), "time-varying spatial traffic state and congestion propagation."),
                tags$li(strong("Results — "), "network performance and link diagnostics."),
                tags$li(strong("Model — "), "equations, assumptions and implementation notes.")
              )
            ),
            div(class = "lift-card",
              p(class = "lift-section-kicker", "Closing note"),
              h2(class = "lift-card-title", "Designed for research iteration"),
              p(class = "lift-card-subtitle", "The interface is intentionally modular so that the traffic-flow formulation can evolve as the research model becomes more specific."),
              div(class = "lift-callout green",
                strong("Keep the engine honest: "), "when a thesis assumption changes, update the corresponding simulation function and let the same visual framework expose its effect on the network."
              )
            )
          )
        )
      )
    )
  )
)

# ============================================================================
# 5. SERVER
# ============================================================================

server <- function(input, output, session) {

  # Warn only when there is neither a cached nor live verified OSM centreline.
  # Once the correct route has been cached, this notification never appears.
  if (grepl("emergency built-in", LYNNWOOD_ROUTE_SOURCE, fixed = TRUE)) {
    showNotification(
      paste0(
        "Lynnwood Road geometry could not be retrieved on this launch and no ",
        "verified local cache exists yet. Re-run TraffiX once while connected ",
        "to the internet; the successful road geometry will then be saved and ",
        "reused permanently."
      ),
      type = "warning",
      duration = 12
    )
  }


  # Custom top navigation -> actual shinydashboard tab state.
  observeEvent(input$lift_nav, {
    req(input$lift_nav)
    updateTabItems(session, "tabs", selected = input$lift_nav)
  }, ignoreInit = TRUE)

  # The current research app uses one fixed Lynnwood Road corridor.
  # Setup therefore exposes only the four parameters that directly drive the
  # implemented traffic equations.
  net <- reactive({
    build_network("corridor", 8, 42)
  })

  fd_live <- reactive({
    fd_params(input$l_veh, input$g_gap, input$r_headway, input$wave_factor)
  })

  # ---- Modern dashboard KPI outputs ----------------------------------------
  output$home_speed <- renderText({
    paste0(round(fd_live()$vf * 3.6, 1), " km/h")
  })

  output$home_density <- renderText({
    paste0(round(fd_live()$kjam * 1000, 1), " veh/km")
  })

  output$home_capacity <- renderText({
    paste0(round(fd_live()$qmax * 3600), " veh/h")
  })

  output$setup_live_summary <- renderUI({
    fd <- fd_live()

    tagList(
      div(class = "setup-derived-grid",
        div(class = "setup-derived-item",
          div(class = "setup-derived-label", "Effective spacing"),
          div(class = "setup-derived-value",
              sprintf("%.2f m", fd$l_eff))
        ),
        div(class = "setup-derived-item",
          div(class = "setup-derived-label", "Free-flow speed"),
          div(class = "setup-derived-value",
              sprintf("%.1f km/h", fd$vf * 3.6))
        ),
        div(class = "setup-derived-item",
          div(class = "setup-derived-label", "Backward wave speed"),
          div(class = "setup-derived-value",
              sprintf("%.1f km/h", fd$w * 3.6))
        )
      )
    )
  })

  output$fd_kc <- renderText({
    paste0(round(fd_live()$kc * 1000, 1), "")
  })

  output$fd_qmax <- renderText({
    paste0(round(fd_live()$qmax * 3600), "")
  })

  output$fd_w <- renderText({
    paste0(round(fd_live()$w, 3), "")
  })

  `%||%` <- function(a, b) if (is.null(a)) b else a

  # Collect only the four active research parameters. A short debounce avoids
  # repeatedly rerunning the CTM while a slider is still being dragged.
  active_parameters <- debounce(
    reactive({
      list(
        l_veh = input$l_veh,
        g_gap = input$g_gap,
        r_headway = input$r_headway,
        wave_factor = input$wave_factor
      )
    }),
    millis = 250
  )

  # No Run Simulation button is required. The model is recomputed
  # automatically whenever one of the four active parameters changes.
  sim_result <- reactive({
    p <- active_parameters()
    req(p$l_veh, p$g_gap, p$r_headway, p$wave_factor)

    simulate_network(
      net = net(),
      l_veh = p$l_veh,
      g_gap = p$g_gap,
      r = p$r_headway,
      wave_factor = p$wave_factor,
      demand_veh_h = 900,
      cycle_length = 60,
      green_split = 0.50,
      signalize = TRUE,
      duration_min = 10,
      incident_node = NULL,
      incident_factor = 1
    )
  })

  sim_summary <- reactive({
    req(sim_result())
    summarise_sim(sim_result())
  })

  # ---- time slider -----------------------------------------------------
  output$time_slider_ui <- renderUI({
    s <- sim_result()
    sliderInput(
      "t_scrub", "Time (s)",
      min = 0,
      max = round(max(s$time_axis)),
      value = 0,
      step = max(0.5, round(s$dt / 2, 1)),
      animate = FALSE
    )
  })

  # Playhead kept on the server so animation frames no longer wait for a slider
  # round-trip. The slider is only refreshed occasionally, for display.
  t_play <- reactiveVal(0)
  anim_state <- new.env(parent = emptyenv())
  anim_state$last <- NULL
  anim_state$n <- 0L

  # User dragging the slider moves the playhead. While animating, small
  # differences are just the slider echoing an older playhead value.
  observeEvent(input$t_scrub, {
    v <- as.numeric(input$t_scrub)
    s <- tryCatch(sim_result(), error = function(e) NULL)
    tol <- if (is.null(s)) 0 else 0.08 * (max(s$time_axis) - min(s$time_axis))
    if (!isTRUE(input$animate) || abs(v - t_play()) > tol) t_play(v)
  }, ignoreInit = TRUE)

  observe({
    if (!isTRUE(input$animate)) {
      anim_state$last <- NULL
      return()
    }
    s <- sim_result(); req(s)
    isolate({
      now <- proc.time()[["elapsed"]]
      elapsed <- if (is.null(anim_state$last)) 0 else min(now - anim_state$last, 0.5)
      anim_state$last <- now

      # One full corridor loop takes target_loop_s real seconds, paced by the
      # wall clock so it stays the same speed even if a frame is slow.
      target_loop_s <- 24
      t_min <- min(s$time_axis); t_max <- max(s$time_axis)
      span <- t_max - t_min
      nxt <- t_play() + span / target_loop_s * elapsed
      if (nxt > t_max) nxt <- t_min + (nxt - t_max) %% span
      t_play(nxt)

      anim_state$n <- anim_state$n + 1L
      if (anim_state$n %% 5L == 0L) {
        updateSliderInput(session, "t_scrub", value = round(nxt, 1))
      }
    })
    invalidateLater(100, session)
  })

  # When playback stops, sync the slider to the exact playhead.
  observeEvent(input$animate, {
    if (!isTRUE(input$animate)) {
      updateSliderInput(session, "t_scrub", value = round(t_play(), 1))
    }
  }, ignoreInit = TRUE)

  current_idx <- reactive({
    s <- sim_result(); req(s)
    idx <- which.min(abs(s$time_axis - t_play()))
    idx
  })

  # ---- shared network state for the diagram and geographic map ------------
  net_state <- reactive({
    n <- net(); g <- n$graph
    s <- tryCatch(sim_result(), error = function(e) NULL)

    if (!is.null(s)) {
      # Interpolate between adjacent simulation states. The playback slider can
      # now move at half-dt increments, so this prevents visible state jumps.
      tcur <- as.numeric(t_play())
      tcur <- max(min(tcur, max(s$time_axis)), min(s$time_axis))

      hi <- which(s$time_axis >= tcur)[1]
      lo <- tail(which(s$time_axis <= tcur), 1)
      if (length(lo) == 0 || is.na(lo)) lo <- 1
      if (length(hi) == 0 || is.na(hi)) hi <- length(s$time_axis)

      k_lo <- matrix(
        s$k_hist[lo, , ],
        nrow = ecount(g),
        ncol = s$ncells
      )
      k_hi <- matrix(
        s$k_hist[hi, , ],
        nrow = ecount(g),
        ncol = s$ncells
      )

      if (hi == lo || abs(s$time_axis[hi] - s$time_axis[lo]) < 1e-12) {
        alpha <- 0
      } else {
        alpha <- (tcur - s$time_axis[lo]) /
          (s$time_axis[hi] - s$time_axis[lo])
      }

      kt <- (1 - alpha) * k_lo + alpha * k_hi

      cell_density <- kt / s$fd$kjam
      edge_k <- rowMeans(kt)
      edge_density <- rowMeans(cell_density)

      cell_speed <- speed_fn(
        kt, s$fd$vf, s$fd$w, s$fd$kjam, s$fd$kc
      )
      if (is.null(dim(cell_speed))) {
        cell_speed <- matrix(cell_speed, nrow = ecount(g))
      }
      edge_speed <- rowMeans(cell_speed) * 3.6

      # Full triangular fundamental-diagram flow:
      # q(k) = min(v_f k, w(k_jam - k), q_max).
      #
      # IMPORTANT: keep the matrix as the FIRST argument to pmax(). R's
      # pmax/pmin copy dimensions from their first argument. The previous
      # pmax(0, matrix) call therefore dropped dim(cell_fd_flow), which made
      # rowMeans() fail with:
      #   "'x' must be an array of at least two dimensions".
      cell_fd_flow <- pmin(
        s$fd$vf * kt,
        s$fd$w * (s$fd$kjam - kt),
        s$fd$qmax
      )
      cell_fd_flow <- pmax(cell_fd_flow, 0)

      # Defensive safeguard in case a future one-cell configuration causes
      # dimensional simplification elsewhere.
      if (is.null(dim(cell_fd_flow))) {
        cell_fd_flow <- matrix(cell_fd_flow, nrow = ecount(g))
      }

      edge_flow <- rowMeans(cell_fd_flow) * 3600

      vf_display <- s$fd$vf * 3.6
      qmax_display <- s$fd$qmax * 3600
    } else {
      fd0 <- fd_live()
      cell_density <- matrix(
        0.1,
        nrow = ecount(g),
        ncol = 4
      )
      edge_density <- rowMeans(cell_density)
      edge_k <- edge_density * fd0$kjam
      edge_speed <- rep(fd0$vf * 3.6, ecount(g))

      k0 <- 0.1 * fd0$kjam
      q0 <- pmax(
        0,
        pmin(
          fd0$vf * k0,
          fd0$w * (fd0$kjam - k0),
          fd0$qmax
        )
      ) * 3600
      edge_flow <- rep(q0, ecount(g))
      cell_speed <- matrix(
        fd0$vf * 3.6,
        nrow = ecount(g),
        ncol = ncol(cell_density)
      )
      cell_fd_flow <- matrix(
        q0 / 3600,
        nrow = ecount(g),
        ncol = ncol(cell_density)
      )

      vf_display <- fd0$vf * 3.6
      qmax_display <- fd0$qmax * 3600
    }

    # Fixed model-based colour domains are retained, but density now uses a
    # piecewise absolute scale: 0% jam = green, 20% = amber, 50% = red.
    # This makes meaningful link-to-link differences easier to see without
    # reverting to misleading per-frame min/max rescaling.
    mode <- input$network_metric %||% "density"

    # Ensure cell-level speed/flow objects exist in the fallback state too.
    if (!exists("cell_speed") || is.null(dim(cell_speed))) {
      cell_speed <- matrix(
        edge_speed,
        nrow = ecount(g),
        ncol = length(edge_speed) / ecount(g)
      )
    }
    if (!exists("cell_fd_flow") || is.null(dim(cell_fd_flow))) {
      cell_fd_flow <- matrix(
        rep(edge_flow, each = ncol(cell_density)),
        nrow = ecount(g),
        byrow = TRUE
      ) / 3600
    }

    n_edges <- ecount(g)
    n_cells <- ncol(cell_density)

    if (mode == "speed") {
      metric_values <- edge_speed
      metric_label <- "Speed (km/h)"
      pal <- colorRampPalette(
        c("#D83A37", "#F08A32", "#E6B83E", "#76B985", "#2ECC71")
      )(256)

      cell_metric <- matrix(
        cell_speed,
        nrow = n_edges,
        ncol = n_cells
      )

      # Keep the matrix as the first argument to pmin/pmax so its dimensions
      # survive. Then explicitly reshape as a final safeguard.
      cell_scaled <- pmin(
        cell_metric / max(vf_display, 1e-12),
        1
      )
      cell_scaled <- pmax(cell_scaled, 0)
      cell_scaled <- matrix(
        cell_scaled,
        nrow = n_edges,
        ncol = n_cells
      )

      scaled <- rowMeans(cell_scaled)
      reverse_scale <- TRUE

    } else if (mode == "flow") {
      metric_values <- edge_flow
      metric_label <- "FD flow potential (veh/h)"
      pal <- colorRampPalette(
        c("#D83A37", "#F08A32", "#E6B83E", "#76B985", "#2ECC71")
      )(256)

      cell_metric <- matrix(
        cell_fd_flow * 3600,
        nrow = n_edges,
        ncol = n_cells
      )

      cell_scaled <- pmin(
        cell_metric / max(qmax_display, 1e-12),
        1
      )
      cell_scaled <- pmax(cell_scaled, 0)
      cell_scaled <- matrix(
        cell_scaled,
        nrow = n_edges,
        ncol = n_cells
      )

      scaled <- rowMeans(cell_scaled)
      reverse_scale <- TRUE

    } else {
      metric_values <- edge_density
      metric_label <- "Density (% of jam)"
      pal <- colorRampPalette(
        c("#2ECC71", "#8BC34A", "#F5A623", "#F0782B", "#E63946")
      )(256)

      cell_metric <- matrix(
        cell_density,
        nrow = n_edges,
        ncol = n_cells
      )

      # Dimension-safe piecewise absolute density scale:
      #   0% jam  -> green
      #   20% jam -> amber
      #   50% jam -> red
      #
      # Avoid ifelse() here because it can simplify array attributes.
      cell_scaled <- matrix(
        0,
        nrow = n_edges,
        ncol = n_cells
      )

      low_idx <- cell_metric <= 0.20

      if (any(low_idx)) {
        low_values <- pmax(cell_metric[low_idx], 0)
        cell_scaled[low_idx] <-
          0.50 * low_values / 0.20
      }

      if (any(!low_idx)) {
        high_values <- cell_metric[!low_idx] - 0.20
        high_values <- pmin(high_values, 0.30)
        high_values <- pmax(high_values, 0)

        cell_scaled[!low_idx] <-
          0.50 + 0.50 * high_values / 0.30
      }

      cell_scaled <- pmin(cell_scaled, 1)
      cell_scaled <- pmax(cell_scaled, 0)
      cell_scaled <- matrix(
        cell_scaled,
        nrow = n_edges,
        ncol = n_cells
      )

      scaled <- rowMeans(cell_scaled)
      reverse_scale <- FALSE
    }

    edge_idx_col <- pmax(
      1L,
      pmin(256L, round(scaled * 255) + 1L)
    )
    edge_col <- pal[edge_idx_col]

    cell_idx_col <- pmax(
      1L,
      pmin(256L, round(cell_scaled * 255) + 1L)
    )
    cell_col <- matrix(
      pal[cell_idx_col],
      nrow = n_edges,
      ncol = n_cells
    )

    # A separate absolute density intensity controls line width / node halo
    # size. Red is reached at 50% jam to match the visual legend.
    density_intensity <- pmax(
      0,
      pmin(1, edge_density / 0.50)
    )
    cell_density_intensity <- pmin(
      matrix(
        cell_density,
        nrow = n_edges,
        ncol = n_cells
      ) / 0.50,
      1
    )
    cell_density_intensity <- pmax(
      cell_density_intensity,
      0
    )
    cell_density_intensity <- matrix(
      cell_density_intensity,
      nrow = n_edges,
      ncol = n_cells
    )

    el <- as_edgelist(g, names = FALSE)
    role <- V(g)$role
    node_col <- ifelse(role == "source", "#0FB5AE", ifelse(role == "sink", "#8E44AD", "#0B5FA5"))

    if (!is.null(s) && isTRUE(s$signalize)) {
      tsec <- as.numeric(t_play())
      green <- (tsec %% s$cycle_length) < (s$green_split * s$cycle_length)
      node_col <- ifelse(
        role == "junction",
        ifelse(green, "#2ECC71", "#E63946"),
        node_col
      )
    }

    list(
      g = g, el = el, role = role,
      edge_k = edge_k,
      edge_density = edge_density,
      edge_speed = edge_speed,
      edge_flow = edge_flow,
      cell_density = cell_density,
      cell_speed = cell_speed,
      cell_flow = cell_fd_flow * 3600,
      cell_col = cell_col,
      density_intensity = density_intensity,
      cell_density_intensity = cell_density_intensity,
      metric_values = metric_values,
      metric_label = metric_label,
      reverse_scale = reverse_scale,
      edge_col = edge_col,
      node_col = node_col
    )
  })

  # ---- Lynnwood Road traffic exposure map ---------------------------------
  # The basemap and corridor are real-world Pretoria geography. Simulation
  # nodes are positioned along that corridor for visual communication only.
  output$net_map <- renderLeaflet({
    leaflet(options = leafletOptions(
      zoomControl = TRUE,
      minZoom = 12,
      maxZoom = 19,
      preferCanvas = FALSE
    )) %>%
      # Use the standard OpenStreetMap tile layer used in the earlier build.
      # It does not require a CARTO API key. The Lynnwood Road centreline is
      # obtained separately above from keyless OSRM/OpenStreetMap road geometry.
      addTiles(
        urlTemplate = "https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png",
        attribution = '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
        options = tileOptions(noWrap = TRUE),
        group = "Basemap"
      ) %>%
      addPolylines(
        data = LYNNWOOD_ROUTE,
        lng = ~lon, lat = ~lat,
        color = "#182d23", weight = 12, opacity = 0.12,
        group = "Lynnwood corridor",
        options = pathOptions(interactive = FALSE)
      ) %>%
      addPolylines(
        data = LYNNWOOD_ROUTE,
        lng = ~lon, lat = ~lat,
        color = "#787265", weight = 2.5, opacity = 0.65,
        dashArray = "6,6",
        group = "Lynnwood corridor",
        options = pathOptions(interactive = FALSE)
      ) %>%
      addPolylines(
        data = LYNNWOOD_ROUTE,
        lng = ~lon, lat = ~lat,
        color = "#ffffff",
        weight = 10,
        opacity = 0.78,
        group = "Traffic underlay",
        options = pathOptions(interactive = FALSE)
      ) %>%
      addLabelOnlyMarkers(
        lng = c(LYNNWOOD_ROUTE$lon[1], LYNNWOOD_ROUTE$lon[nrow(LYNNWOOD_ROUTE)]),
        lat = c(LYNNWOOD_ROUTE$lat[1], LYNNWOOD_ROUTE$lat[nrow(LYNNWOOD_ROUTE)]),
        label = c("UP / Roper St", "Lynnwood Bridge / N1"),
        labelOptions = labelOptions(
          noHide = TRUE,
          textOnly = TRUE,
          direction = "top",
          style = list(
            "font-family" = "Inter, sans-serif",
            "font-size" = "11px",
            "font-weight" = "600",
            "color" = "#182d23",
            "text-shadow" = "0 0 5px #ffffff, 0 0 5px #ffffff"
          )
        ),
        group = "Landmarks"
      ) %>%
      fitBounds(
        lng1 = min(LYNNWOOD_ROUTE$lon) - 0.003,
        lat1 = min(LYNNWOOD_ROUTE$lat) - 0.003,
        lng2 = max(LYNNWOOD_ROUTE$lon) + 0.003,
        lat2 = max(LYNNWOOD_ROUTE$lat) + 0.003
      )
  })

  outputOptions(output, "net_map", suspendWhenHidden = FALSE)

  map_selected <- reactiveVal(NULL)

  # Desktop interaction: update the inspector immediately on hover.
  # Leaflet sends polylines through *_shape_mouseover and circle markers
  # through *_marker_mouseover.
  observeEvent(input$net_map_shape_mouseover, {
    hover <- input$net_map_shape_mouseover
    if (is.null(hover$id) || !nzchar(hover$id)) return()
    map_selected(as.character(hover$id))
  }, ignoreInit = TRUE)

  observeEvent(input$net_map_marker_mouseover, {
    hover <- input$net_map_marker_mouseover
    if (is.null(hover$id) || !nzchar(hover$id)) return()
    map_selected(as.character(hover$id))
  }, ignoreInit = TRUE)

  # Keep click/tap support as a mobile and accessibility fallback.
  observeEvent(input$net_map_shape_click, {
    click <- input$net_map_shape_click
    if (is.null(click$id) || !nzchar(click$id)) return()
    map_selected(as.character(click$id))
  }, ignoreInit = TRUE)

  observeEvent(input$net_map_marker_click, {
    click <- input$net_map_marker_click
    if (is.null(click$id) || !nzchar(click$id)) return()
    map_selected(as.character(click$id))
  }, ignoreInit = TRUE)

  output$map_selection <- renderUI({
    ns <- net_state()
    n <- net()
    g <- n$graph
    id <- map_selected()

    if (is.null(id)) {
      return(div(class = "lift-map-selection empty",
        "Hover over a road link or node to inspect its live state. Tap also works on touch devices."
      ))
    }

    # Double-buffered live layers carry a "__A"/"__B" suffix. Remove it
    # before interpreting the selected map element.
    base_id <- sub("__.*$", "", id)

    if (grepl("^link_", base_id)) {
      m <- regexec(
        "^link_([0-9]+)(?:_cell_([0-9]+))?$",
        base_id
      )
      parts <- regmatches(base_id, m)[[1]]

      if (length(parts) < 2) {
        return(div(class = "lift-map-selection empty", "Selection unavailable."))
      }

      edge_id <- suppressWarnings(as.integer(parts[2]))
      cell_id <- if (length(parts) >= 3 && nzchar(parts[3])) {
        suppressWarnings(as.integer(parts[3]))
      } else {
        NA_integer_
      }

      if (is.na(edge_id) || edge_id < 1 || edge_id > nrow(ns$el)) {
        return(div(class = "lift-map-selection empty", "Selection unavailable."))
      }

      from <- ns$el[edge_id, 1]
      to <- ns$el[edge_id, 2]

      use_cell <- !is.na(cell_id) &&
        cell_id >= 1 &&
        cell_id <= ncol(ns$cell_density)

      density_value <- if (use_cell) {
        ns$cell_density[edge_id, cell_id]
      } else {
        ns$edge_density[edge_id]
      }
      speed_value <- if (use_cell) {
        ns$cell_speed[edge_id, cell_id]
      } else {
        ns$edge_speed[edge_id]
      }
      flow_value <- if (use_cell) {
        ns$cell_flow[edge_id, cell_id]
      } else {
        ns$edge_flow[edge_id]
      }
      dot_colour <- if (use_cell) {
        ns$cell_col[edge_id, cell_id]
      } else {
        ns$edge_col[edge_id]
      }

      title <- if (use_cell) {
        paste0(
          "Link ", edge_id, " · Cell ", cell_id,
          " · N", from, " → N", to
        )
      } else {
        paste0("Link ", edge_id, " · N", from, " → N", to)
      }

      return(div(class = "lift-map-selection",
        div(class = "lift-map-chip",
          span(
            class = "lift-map-dot",
            style = paste0("background:", dot_colour, ";")
          ),
          if (use_cell) "Road-link cell" else "Road link"
        ),
        div(class = "lift-network-selection-title", title),
        div(class = "lift-network-detail-grid",
          div(
            div(class = "lift-network-detail-label", "Link length"),
            div(
              class = "lift-network-detail-value",
              paste0(E(g)$length_m[edge_id], " m")
            )
          ),
          div(
            div(class = "lift-network-detail-label", "Density"),
            div(
              class = "lift-network-detail-value",
              paste0(round(density_value * 100, 1), "% of jam")
            )
          ),
          div(
            div(class = "lift-network-detail-label", "Speed"),
            div(
              class = "lift-network-detail-value",
              paste0(round(speed_value, 1), " km/h")
            )
          ),
          div(
            div(class = "lift-network-detail-label", "FD flow potential"),
            div(
              class = "lift-network-detail-value",
              paste0(round(flow_value), " veh/h")
            )
          )
        )
      ))
    }

    if (grepl("^node_", base_id)) {
      node_id <- suppressWarnings(
        as.integer(sub("^node_", "", base_id))
      )
      if (is.na(node_id) || node_id < 1 || node_id > vcount(g)) {
        return(div(class = "lift-map-selection empty", "Selection unavailable."))
      }
      role <- V(g)$role[node_id]
      incident_edges <- as.integer(incident(g, node_id, mode = "all"))
      local_density <- if (length(incident_edges)) mean(ns$edge_density[incident_edges]) else 0
      return(div(class = "lift-map-selection",
        div(class = "lift-map-chip",
          span(class = "lift-map-dot", style = paste0("background:", ns$node_col[node_id], ";")),
          "Network node"
        ),
        div(class = "lift-network-selection-title", paste0("Node N", node_id)),
        div(class = "lift-network-detail-grid",
          div(div(class = "lift-network-detail-label", "Role"), div(class = "lift-network-detail-value", toupper(role))),
          div(div(class = "lift-network-detail-label", "Connected links"), div(class = "lift-network-detail-value", length(incident_edges))),
          div(div(class = "lift-network-detail-label", "Local density"), div(class = "lift-network-detail-value", paste0(round(local_density * 100, 1), "% of jam"))),
          div(div(class = "lift-network-detail-label", "Study corridor"), div(class = "lift-network-detail-value", "Lynnwood Road"))
        )
      ))
    }

    div(class = "lift-map-selection empty", "Hover over a road link or node to inspect its live state. Tap also works on touch devices.")
  })

  # The road cells and nodes are drawn ONCE (and again only if the simulation
  # is recomputed). Animation frames then just restyle those existing layers in
  # the browser, so nothing is cleared or redrawn: no flashing, and far less
  # data sent per frame.
  observe({
    s_now <- tryCatch(sim_result(), error = function(e) NULL)
    ns <- isolate(net_state())
    n <- isolate(net())
    g <- n$graph
    ll <- lynnwood_node_positions(vcount(g))
    el <- ns$el

    node_density <- vapply(seq_len(vcount(g)), function(v) {
      ie <- as.integer(incident(g, v, mode = "all"))
      if (length(ie) == 0) 0 else mean(ns$edge_density[ie], na.rm = TRUE)
    }, numeric(1))
    node_density[!is.finite(node_density)] <- 0
    node_intensity <- pmax(0, pmin(1, node_density / 0.50))

    proxy <- leafletProxy("net_map") %>%
      clearGroup("Traffic cells") %>%
      clearGroup("Traffic nodes")

    # Build all cell geometry in one pass, then add each cell once.
    cell_ids <- character(0)
    cell_heads <- character(0)
    for (i in seq_len(nrow(el))) {
      line_df <- lynnwood_edge_path(
        from_node = el[i, 1], to_node = el[i, 2], n_nodes = vcount(g)
      )
      cell_paths <- split_road_path_into_cells(line_df, ncol(ns$cell_density))

      for (j in seq_along(cell_paths)) {
        id <- paste0("link_", i, "_cell_", j)
        head <- paste0(
          "<b>Link ", i, " \u00b7 Cell ", j,
          " \u00b7 N", el[i, 1], " \u2192 N", el[i, 2], "</b>"
        )
        cell_ids <- c(cell_ids, id)
        cell_heads <- c(cell_heads, head)

        proxy <- proxy %>%
          addPolylines(
            data = cell_paths[[j]], lng = ~lon, lat = ~lat,
            layerId = id,
            color = ns$cell_col[i, j],
            weight = 4.5 + 8.5 * ns$cell_density_intensity[i, j],
            opacity = 0.97,
            group = "Traffic cells",
            label = HTML(paste0(
              head,
              "<br>Density: ", round(ns$cell_density[i, j] * 100, 1), "% of jam",
              "<br>Speed: ", round(ns$cell_speed[i, j], 1), " km/h",
              "<br>FD flow potential: ", round(ns$cell_flow[i, j]), " veh/h"
            )),
            options = pathOptions(className = "traffix-live-shape")
          )
      }
    }

    proxy <- proxy %>%
      addCircleMarkers(
        lng = ll$lon, lat = ll$lat,
        layerId = paste0("halo_", seq_len(vcount(g))),
        radius = 11 + 13 * node_intensity,
        stroke = FALSE,
        fillColor = ns$node_col, fillOpacity = 0.13,
        group = "Traffic nodes",
        options = pathOptions(interactive = FALSE, className = "traffix-live-shape")
      ) %>%
      addCircleMarkers(
        lng = ll$lon, lat = ll$lat,
        layerId = paste0("node_", seq_len(vcount(g))),
        radius = 7 + 5 * node_intensity,
        color = "#ffffff", weight = 2,
        fillColor = ns$node_col, fillOpacity = 0.98,
        group = "Traffic nodes",
        label = paste0("N", V(g)$name, " \u00b7 ", toupper(ns$role)),
        options = pathOptions(className = "traffix-live-shape")
      )

    session$sendCustomMessage("traffix_heads", list(ids = cell_ids, heads = cell_heads))
  })

  # Per-frame update: only small numeric vectors are sent to the browser.
  observe({
    ns <- net_state()
    g <- ns$g
    n_nodes <- vcount(g)
    n_cells <- ncol(ns$cell_density)
    el <- ns$el

    # Same ordering as the draw observer: link i, then cell j.
    ids <- as.vector(t(outer(seq_len(nrow(el)), seq_len(n_cells),
                             function(i, j) paste0("link_", i, "_cell_", j))))
    flat <- function(m) as.vector(t(m))

    node_density <- vapply(seq_len(n_nodes), function(v) {
      ie <- as.integer(incident(g, v, mode = "all"))
      if (length(ie) == 0) 0 else mean(ns$edge_density[ie], na.rm = TRUE)
    }, numeric(1))
    node_density[!is.finite(node_density)] <- 0
    node_intensity <- pmax(0, pmin(1, node_density / 0.50))

    session$sendCustomMessage("traffix_style", list(
      ids = ids,
      color = flat(ns$cell_col),
      weight = round(4.5 + 8.5 * flat(ns$cell_density_intensity), 2),
      dens = round(flat(ns$cell_density) * 100, 1),
      speed = round(flat(ns$cell_speed), 1),
      flow = round(flat(ns$cell_flow)),
      node_ids = paste0("node_", seq_len(n_nodes)),
      node_fill = ns$node_col,
      node_radius = round(7 + 5 * node_intensity, 2),
      halo_radius = round(11 + 13 * node_intensity, 2)
    ))
  })

  # Legends only depend on the selected metric. They no longer get destroyed
  # and recreated at every animation frame, which removes another source of
  # visible flicker.
  observe({
    mode <- input$network_metric %||% "density"

    if (mode == "speed") {
      legend_labels <- c(
        "Low speed",
        "Mid-range",
        "Near free-flow"
      )
      legend_cols <- c(
        "#D83A37",
        "#E6B83E",
        "#2ECC71"
      )
      legend_title <- "Speed · fixed 0 to V\u2091"
    } else if (mode == "flow") {
      legend_labels <- c(
        "Low potential",
        "Moderate",
        "Near capacity"
      )
      legend_cols <- c(
        "#D83A37",
        "#E6B83E",
        "#2ECC71"
      )
      legend_title <- "FD flow potential · 0 to capacity"
    } else {
      legend_labels <- c(
        "Low · 0–10% jam",
        "Building · 10–20%",
        "Moderate · 20–35%",
        "High · 35–50%+"
      )
      legend_cols <- c(
        "#2ECC71",
        "#8BC34A",
        "#F5A623",
        "#E63946"
      )
      legend_title <- "Density · absolute % of jam"
    }

    leafletProxy("net_map") %>%
      clearControls() %>%
      addLegend(
        position = "bottomright",
        colors = legend_cols,
        labels = legend_labels,
        title = legend_title,
        opacity = 0.95
      ) %>%
      addLegend(
        position = "bottomleft",
        colors = c(
          "#0FB5AE",
          "#8E44AD",
          "#2ECC71",
          "#E63946"
        ),
        labels = c(
          "Source",
          "Sink",
          "Junction — green",
          "Junction — red"
        ),
        title = "Node role / phase",
        opacity = 0.95
      )
  })

  output$phase_readout <- renderText({
    s <- tryCatch(sim_result(), error = function(e) NULL)
    req(s)

    tcur <- as.numeric(t_play())
    tcur <- max(min(tcur, max(s$time_axis)), min(s$time_axis))

    hi <- which(s$time_axis >= tcur)[1]
    lo <- tail(which(s$time_axis <= tcur), 1)
    if (length(lo) == 0 || is.na(lo)) lo <- 1
    if (length(hi) == 0 || is.na(hi)) hi <- length(s$time_axis)

    if (hi == lo || abs(s$time_axis[hi] - s$time_axis[lo]) < 1e-12) {
      alpha <- 0
    } else {
      alpha <- (tcur - s$time_axis[lo]) /
        (s$time_axis[hi] - s$time_axis[lo])
    }

    k_lo <- matrix(
      s$k_hist[lo, , ],
      nrow = dim(s$k_hist)[2],
      ncol = s$ncells
    )
    k_hi <- matrix(
      s$k_hist[hi, , ],
      nrow = dim(s$k_hist)[2],
      ncol = s$ncells
    )
    kt <- (1 - alpha) * k_lo + alpha * k_hi

    veh_now <- sum(
      kt *
        matrix(
          s$dx,
          nrow = dim(s$k_hist)[2],
          ncol = s$ncells
        )
    )
    exits_now <- (1 - alpha) * s$throughput[lo] +
      alpha * s$throughput[hi]

    HTML(paste0(
      "<b>t = ", round(tcur, 1), " s</b><br>",
      "Vehicles in network: ", round(veh_now), "<br>",
      "Cumulative exits: ", round(exits_now)
    ))
  })

  output$derived_eqns <- renderUI({
    fd <- fd_live()
    withMathJax(
      p(sprintf("$$l^{\\mathrm{eff}} = %.1f + %.1f = %.2f\\text{ m}$$", input$l_veh, input$g_gap, fd$l_eff)),
      p(sprintf("$$V^{\\mathrm{space}} = %.2f / %.2f = %.2f\\text{ m/s} \\;(%.1f\\text{ km/h})$$",
                fd$l_eff, input$r_headway, fd$vf, fd$vf * 3.6)),
      p(sprintf("$$k_{\\text{jam}} = 1/l^{\\mathrm{eff}} = %.4f\\text{ veh/m} \\;(%.0f\\text{ veh/km})$$",
                fd$kjam, fd$kjam * 1000))
    )
  })

  # ---- tidy research outputs / CSV exports -------------------------------
  # These reactives convert the internal simulation arrays into ordinary
  # data frames that can be saved, analysed in R, or imported into LaTeX/Excel.

  network_time_series_df <- reactive({
    s <- sim_result()
    ks <- sim_summary()

    data.frame(
      time_s = s$time_axis,
      time_min = s$time_axis / 60,
      avg_speed_kmh = ks$avg_speed_t * 3.6,
      vehicles_in_network = ks$veh_in_net_t,
      cumulative_delay_veh_h = ks$cum_delay_veh_h,
      cumulative_exits_veh = ks$throughput,
      signal_green = if (isTRUE(s$signalize)) {
        (s$time_axis %% s$cycle_length) <
          (s$green_split * s$cycle_length)
      } else {
        rep(TRUE, length(s$time_axis))
      },
      check.names = FALSE
    )
  })

  link_time_series_df <- reactive({
    s <- sim_result()
    g <- net()$graph
    el <- as_edgelist(g, names = FALSE)

    nT <- length(s$time_axis)
    E_n <- ecount(g)

    rows <- vector("list", E_n)
    for (e in seq_len(E_n)) {
      k_e <- s$k_hist[, e, , drop = FALSE]
      k_e <- matrix(k_e, nrow = nT, ncol = s$ncells)
      v_e <- speed_fn(k_e, s$fd$vf, s$fd$w, s$fd$kjam, s$fd$kc)
      if (is.null(dim(v_e))) v_e <- matrix(v_e, nrow = nT)

      veh_e <- k_e * matrix(
        s$dx[e], nrow = nT, ncol = s$ncells
      )
      veh_total <- rowSums(veh_e)
      speed_weighted <- rowSums(v_e * veh_e) / pmax(veh_total, 1e-12)
      speed_weighted[veh_total <= 1e-12] <- s$fd$vf

      congested_mask <- k_e > s$fd$kc
      congested_veh <- rowSums(veh_e * congested_mask)

      rows[[e]] <- data.frame(
        time_s = s$time_axis,
        time_min = s$time_axis / 60,
        Link = e,
        From = el[e, 1],
        To = el[e, 2],
        length_m = s$edge_len[e],
        avg_density_veh_km = rowMeans(k_e) * 1000,
        max_cell_density_veh_km = apply(k_e, 1, max) * 1000,
        avg_speed_kmh = speed_weighted * 3.6,
        vehicles_on_link = veh_total,
        vehicles_in_congested_cells = congested_veh,
        inflow_veh_h = s$entry_flow_hist[, e] * 3600,
        outflow_veh_h = s$exit_flow_hist[, e] * 3600,
        upstream_density_veh_km = k_e[, 1] * 1000,
        downstream_density_veh_km = k_e[, s$ncells] * 1000,
        signal_green = if (isTRUE(s$signalize)) {
          (s$time_axis %% s$cycle_length) <
            (s$green_split * s$cycle_length)
        } else {
          rep(TRUE, nT)
        },
        check.names = FALSE
      )
    }

    do.call(rbind, rows)
  })

  link_summary_df <- reactive({
    s <- sim_result()
    ks <- sim_summary()
    g <- net()$graph
    el <- as_edgelist(g, names = FALSE)

    data.frame(
      Link = seq_len(nrow(el)),
      From = el[, 1],
      To = el[, 2],
      `Length (m)` = E(g)$length_m,
      `Avg density (veh/km)` = ks$edge_avg_k * 1000,
      `Max density (veh/km)` = ks$edge_max_k * 1000,
      `Avg speed (km/h)` = ks$edge_avg_v * 3.6,
      check.names = FALSE
    )
  })

  cell_state_df <- reactive({
    s <- sim_result()
    g <- net()$graph
    el <- as_edgelist(g, names = FALSE)

    nT <- length(s$time_axis)
    E_n <- ecount(g)
    ncells <- s$ncells

    # expand.grid ordering matches as.vector(k_hist): time varies fastest,
    # followed by link and then cell for an array with dimensions
    # [time, edge, cell].
    idx <- expand.grid(
      time_index = seq_len(nT),
      Link = seq_len(E_n),
      Cell = seq_len(ncells),
      KEEP.OUT.ATTRS = FALSE,
      stringsAsFactors = FALSE
    )

    density_veh_m <- as.vector(s$k_hist)
    speed_m_s <- speed_fn(
      density_veh_m, s$fd$vf, s$fd$w, s$fd$kjam, s$fd$kc
    )
    fd_flow_veh_s <- pmin(
      s$fd$vf * density_veh_m,
      s$fd$w * (s$fd$kjam - density_veh_m),
      s$fd$qmax
    )
    fd_flow_veh_s <- pmax(fd_flow_veh_s, 0)

    data.frame(
      time_s = s$time_axis[idx$time_index],
      time_min = s$time_axis[idx$time_index] / 60,
      Link = idx$Link,
      Cell = idx$Cell,
      From = el[idx$Link, 1],
      To = el[idx$Link, 2],
      cell_length_m = s$dx[idx$Link],
      density_veh_km = density_veh_m * 1000,
      density_pct_jam = 100 * density_veh_m / s$fd$kjam,
      speed_kmh = speed_m_s * 3.6,
      fd_flow_potential_veh_h = fd_flow_veh_s * 3600,
      vehicles_in_cell = density_veh_m * s$dx[idx$Link],
      signal_green = if (isTRUE(s$signalize)) {
        (s$time_axis[idx$time_index] %% s$cycle_length) <
          (s$green_split * s$cycle_length)
      } else {
        rep(TRUE, nrow(idx))
      },
      check.names = FALSE
    )
  })

  simulation_parameters_df <- reactive({
    s <- sim_result()
    p <- active_parameters()

    data.frame(
      parameter = c(
        "vehicle_length_m", "standstill_gap_m", "reaction_time_s",
        "wave_factor", "demand_veh_h", "cycle_length_s",
        "green_split", "duration_min", "n_cells_per_link",
        "effective_spacing_m", "free_flow_speed_kmh",
        "jam_density_veh_km", "critical_density_veh_km",
        "backward_wave_speed_kmh", "capacity_veh_h",
        "simulation_dt_s"
      ),
      value = c(
        p$l_veh, p$g_gap, p$r_headway, p$wave_factor,
        900, 60, 0.50, 10, s$ncells,
        s$fd$l_eff, s$fd$vf * 3.6, s$fd$kjam * 1000,
        s$fd$kc * 1000, s$fd$w * 3.6, s$fd$qmax * 3600, s$dt
      ),
      stringsAsFactors = FALSE
    )
  })

  output$download_time_series <- downloadHandler(
    filename = function() {
      paste0("TraffiX_network_time_series_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(network_time_series_df(), file, row.names = FALSE)
    }
  )

  output$download_link_time_series <- downloadHandler(
    filename = function() {
      paste0("TraffiX_link_time_series_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(link_time_series_df(), file, row.names = FALSE)
    }
  )

  output$download_link_summary <- downloadHandler(
    filename = function() {
      paste0("TraffiX_link_summary_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(link_summary_df(), file, row.names = FALSE)
    }
  )

  output$download_cell_states <- downloadHandler(
    filename = function() {
      paste0("TraffiX_cell_states_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(cell_state_df(), file, row.names = FALSE)
    }
  )

  output$download_parameters <- downloadHandler(
    filename = function() {
      paste0("TraffiX_simulation_parameters_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(simulation_parameters_df(), file, row.names = FALSE)
    }
  )

  # ---- simulation result time series --------------------------------------
  output$speed_t_plot <- renderPlotly({
    s <- sim_result(); ks <- sim_summary()
    plot_ly(x = s$time_axis, y = ks$avg_speed_t * 3.6, type = "scatter", mode = "lines",
            line = list(color = "#0B5FA5")) %>%
      layout(xaxis = list(title = "Time (s)"), yaxis = list(title = "Avg speed (km/h)"), margin = list(t = 10))
  })

  output$veh_t_plot <- renderPlotly({
    s <- sim_result(); ks <- sim_summary()
    plot_ly(x = s$time_axis, y = ks$veh_in_net_t, type = "scatter", mode = "lines",
            fill = "tozeroy", line = list(color = "#0FB5AE")) %>%
      layout(xaxis = list(title = "Time (s)"), yaxis = list(title = "Vehicles"), margin = list(t = 10))
  })

  output$delay_t_plot <- renderPlotly({
    s <- sim_result(); ks <- sim_summary()
    plot_ly(x = s$time_axis, y = ks$cum_delay_veh_h, type = "scatter", mode = "lines",
            line = list(color = "#E63946")) %>%
      layout(xaxis = list(title = "Time (s)"), yaxis = list(title = "Cumulative delay (veh\u00b7h)"), margin = list(t = 10))
  })

  output$throughput_t_plot <- renderPlotly({
    s <- sim_result(); ks <- sim_summary()
    plot_ly(x = s$time_axis, y = ks$throughput, type = "scatter", mode = "lines",
            line = list(color = "#2ECC71")) %>%
      layout(xaxis = list(title = "Time (s)"), yaxis = list(title = "Cumulative exits (veh)"), margin = list(t = 10))
  })

  output$link_table <- renderDT({
    df <- link_summary_df()
    display_df <- df
    display_df$`Avg density (veh/km)` <- round(display_df$`Avg density (veh/km)`, 1)
    display_df$`Max density (veh/km)` <- round(display_df$`Max density (veh/km)`, 1)
    display_df$`Avg speed (km/h)` <- round(display_df$`Avg speed (km/h)`, 1)

    datatable(display_df, options = list(pageLength = 8, dom = "tip"), rownames = FALSE) %>%
      formatStyle(
        "Avg density (veh/km)",
        background = styleColorBar(
          range(display_df$`Avg density (veh/km)`, na.rm = TRUE),
          "#F5A62366"
        )
      )
  })
}

shinyApp(ui, server)

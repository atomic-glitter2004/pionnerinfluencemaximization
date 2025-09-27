using Random

function read_document(path)
    lines = []
    for line in eachline(path)
        stripped_line = strip(line)
        if !isempty(stripped_line) && !startswith(stripped_line, "#")
            push!(lines, stripped_line)
        end
    end
    return lines
end

function load_nodes(path)
    names = read_document(path)
    nodeindices = Dict{String,Int}()
    for (index, name) in enumerate(names)
        nodeindices[name] = index
    end
    return names, nodeindices
end

function load_edges(path, nodeindices)
    edgelist = Tuple{Int,Int,Float64}[]
    lines = read_document(path)
    for line_number in 1:length(lines)
        s = lines[line_number]
        parts = split(s)
        unode = parts[1]
        vnode = parts[2]
        u = get(nodeindices, unode, nothing)
        v = get(nodeindices, vnode, nothing)
        p = 1.0
        if length(parts) >= 3
            p = parse(Float64, parts[3])
        end
        push!(edgelist, (u, v, p))
    end
    return edgelist
end

function build_adj(tnodes, edgelist)
    adj = Vector{Vector{Tuple{Int,Float64}}}(undef, tnodes)
    for i in 1:tnodes
        adj[i] = Tuple{Int,Float64}[]
    end
    for edge in edgelist
        u = edge[1]
        v = edge[2]
        p = edge[3]
        push!(adj[u], (v,p))
    end
    return adj
end

function build_reverse_adj(adj)
    n = length(adj)
    rev = [Tuple{Int,Float64}[] for _ in 1:n]
    edge_w = Dict{Tuple{Int,Int},Float64}()
    for u in 1:n
        for (v,p) in adj[u]
            push!(rev[v], (u,p))
            edge_w[(u,v)] = p
        end
    end
    return rev, edge_w
end


function directed_degrees(adj)
    n = length(adj)
    nout = zeros(Float64, n)
    nin  = zeros(Float64, n)
    m = 0.0
    for u in 1:n
        for (v,p) in adj[u]
            nout[u] = nout[u] + p
            nin[v]  = nin[v] + p
            m = m+p
        end
    end
    return nout, nin, m
end

function directed_modularity(adj, labels; nout, nin, m, edge_w)
    m == 0.0 && return 0.0
    n = length(adj)
    Q = 0.0
    for u in 1:n
        lu = labels[u]
        exeu = nout[u]
        for v in 1:n
            if lu == labels[v]
                Auv = get(edge_w, (u,v), 0.0)
                reev  = nin[v]
                Q = Q + (Auv - (exeu * reev) / m)
            end
        end
    end
    return Q / m
end

function totalneighbors(adj, rev, u)
    out_neighbors = Int[]
    for (v, _) in adj[u]
        push!(out_neighbors, v)
    end

    in_neighbors = Int[]
    for (v, _) in rev[u]
        push!(in_neighbors, v)
    end

    both = union(out_neighbors, in_neighbors)
    return collect(both)
end

function detect_communities_directed_modularity(adj; max_passes=100)
    rev, edge_w = build_reverse_adj(adj)
    nout, nin, m = directed_degrees(adj)
    n = length(adj)
    labels = collect(1:n)
    changed = true
    passes = 0
    while changed && passes < max_passes
        changed = false
        passes  = passes + 1
        for u in Random.shuffle(1:n)
            curc = labels[u]
            best_lbl = curc
            best_Q = directed_modularity(adj, labels; nout=nout, nin=nin, m=m, edge_w=edge_w)
            neighborlabel = Set(labels[v] for v in totalneighbors(adj, rev, u))
            for lbl in neighborlabel
                if lbl == curc; continue; end
                labels[u] = lbl
                Qnew = directed_modularity(adj, labels; nout=nout, nin=nin, m=m, edge_w=edge_w)
                if Qnew > best_Q + 1e-10
                    best_Q = Qnew
                    best_lbl = lbl
                end
            end
            labels[u] = best_lbl
            changed = changed || (best_lbl != curc)
        end
    end
    return Dict(i => labels[i] for i in 1:n)
end

function totals(node, adj, groups)
    total_prob = 0.0
    cross_group_prob = 0.0
    gu = groups[node]
    for (v,p) in adj[node]
        total_prob += p
        if groups[v] != gu
            cross_group_prob += p
        end
    end
    return total_prob, cross_group_prob
end

function group_nodes_map(groups)
    m = Dict{Int, Vector{Int}}()
    for (u,g) in groups
        push!(get!(m, g, Int[]), u)
    end
    return m
end

function community_outflow_vector(adj, groups, Gs)
    idx = Dict(g=>i for (i,g) in enumerate(Gs))
    out = zeros(Float64, length(Gs))
    for u in 1:length(adj)
        gu = groups[u]
        for (v,p) in adj[u]
            gv = groups[v]
            if gv != gu
                out[idx[gu]] = out[idx[gu]] + p
            end
        end
    end
    return out
end

function compute_meta_quotas(k, adj, groups; alpha_size=0.5, alpha_flow=0.5)
    by_group = group_nodes_map(groups)
    Gs = sort(collect(keys(by_group)))
    G = length(Gs)
    sizes = [length(by_group[g]) for g in Gs]
    sizew = sizes ./ sum(sizes)
    flow = community_outflow_vector(adj, groups, Gs)
    floww = sum(flow) > 0 ? flow ./ sum(flow) : fill(1.0/G, G)
    w = alpha_size .* sizew .+ alpha_flow .* floww
    w = w ./ sum(w)  

    quotas = fill(0, G)
    if k >= G
        quotas .= 1
        remaining = k - G
        if remaining > 0
            add = floor.(Int, remaining .* w)
            quotas .+= add
            used = sum(add)
            left = remaining - used
            if left > 0
                rem = (remaining .* w) .- add
                order = sortperm(rem; rev=true)
                for i in 1:left
                    quotas[order[i]] += 1
                end
            end
        end
    else
        order = sortperm(w; rev=true)
        for i in 1:k
            quotas[order[i]] += 1
        end
    end
    return quotas, Gs, by_group
end

function candidates(adj, groups)
    by_group = Dict{Int, Vector{Int}}()
    for (node, group_id) in groups
        if !haskey(by_group, group_id)
            by_group[group_id] = Int[]
        end
        push!(by_group[group_id], node)
    end
    primary_candidates = Int[]
    cross_candidates = Int[]
    for vs in values(by_group)
        best_total = -1.0
        best_total_node = 0
        best_cross = -1.0
        best_cross_node = 0
        for u in vs
            t, c = totals(u, adj, groups)
            if t > best_total
                best_total = t
                best_total_node = u
            end
            if c > best_cross
                best_cross = c
                best_cross_node = u
            end
        end
        push!(primary_candidates, best_total_node)
        push!(cross_candidates, best_cross_node)
    end
    combined_candidates = vcat(primary_candidates, cross_candidates)
    unique_candidates = unique(combined_candidates)
    return unique_candidates
end

function local_spread(seeds, adj; R=40, L=1000)
    tnodes = length(adj)
    total_activated = 0.0
    for _ in 1:R
        active = falses(tnodes)
        frontier = Int[]
        for s in seeds
            if !active[s]
                active[s] = true
                push!(frontier, s)
            end
        end
        depth = 0
        while !isempty(frontier) && depth < L
            next_frontier = Int[]
            for x in frontier
                neighbors = adj[x]
                for (y, p) in neighbors
                    if !active[y]
                        r = rand()
                        if r < p
                            active[y] = true
                            push!(next_frontier, y)
                        end
                    end
                end
            end
            frontier = next_frontier
            depth += 1
        end
        count_active = count(active)
        total_activated += count_active
    end
    average_spread = total_activated / R
    return average_spread
end

function ic_trial_full(seeds, adj)
    tnodes = length(adj)
    active = falses(tnodes)
    frontier = Int[]
    for s in seeds
        if !active[s]
            active[s] = true
            push!(frontier, s)
        end
    end
    while !isempty(frontier)
        next_frontier = Int[]
        for x in frontier
            neighbors = adj[x]
            for (y, p) in neighbors
                if !active[y]
                    r = rand()
                    if r < p
                        active[y] = true
                        push!(next_frontier, y)
                    end
                end
            end
        end
        frontier = next_frontier
    end
    total_active = count(active)
    return total_active
end

function random_seeds(k, tnodes)
    chosen = Set{Int}()
    seeds = Int[]
    while length(seeds) < k && length(chosen) < tnodes
        u = rand(1:tnodes)
        if !(u in chosen)
            push!(seeds, u)
            push!(chosen, u)
        end
    end
    return seeds
end

function pick_seeds_metaquota(k, adj, groups; alpha_size=0.5, alpha_flow=0.5, R=150, L=7, prune_per_group=25)
    quotas, Gs, by_group = compute_meta_quotas(k, adj, groups; alpha_size=alpha_size, alpha_flow=alpha_flow)
    seeds = Int[]
    chosen = Set{Int}()

    for (i,g) in enumerate(Gs)
        q = quotas[i]
        q <= 0 && continue
        cand = setdiff(by_group[g], seeds)
        pre = [(u, totals(u, adj, groups)) for u in cand]  
        pre_sorted = sort(pre; by = x -> (x[2][2], x[2][1]), rev=true)
        if prune_per_group > 0 && length(pre_sorted) > prune_per_group
            cand = first.(pre_sorted[1:prune_per_group])
        else
            cand = first.(pre_sorted)
        end
        while q > 0 && !isempty(cand)
            base = local_spread(seeds, adj; R=R, L=L)
            best_u = 0; best_gain = -Inf
            for u in cand
                if u in chosen; continue; end
                s2 = copy(seeds); push!(s2, u)
                gain = local_spread(s2, adj; R=R, L=L) - base
                if gain > best_gain
                    best_gain = gain
                    best_u = u
                end
            end
            best_u == 0 && break
            push!(seeds, best_u); push!(chosen, best_u)
            q -= 1
            cand = setdiff(cand, [best_u])
        end
    end

    while length(seeds) < k
        all_cand = setdiff(collect(1:length(adj)), seeds)
        pre = [(u, totals(u, adj, groups)) for u in all_cand]
        pre_sorted = sort(pre; by = x -> (x[2][2], x[2][1]), rev=true)
        top = first.(pre_sorted[1:min(length(pre_sorted), prune_per_group)])
        base = local_spread(seeds, adj; R=R, L=L)
        best_u = 0; best_gain = -Inf
        for u in top
            s2 = copy(seeds); push!(s2, u)
            gain = local_spread(s2, adj; R=R, L=L) - base
            if gain > best_gain
                best_gain = gain
                best_u = u
            end
        end
        best_u == 0 && break
        push!(seeds, best_u)
    end

    return seeds
end

nodes_path  = joinpath(@__DIR__, "..", "data", "sharednodes.txt")
edges_path  = joinpath(@__DIR__, "..", "data", "2edges2500.txt")
k = 75

names, nodeindices = load_nodes(nodes_path)
edgelist = load_edges(edges_path, nodeindices)
tnodes = length(names)
adj = build_adj(tnodes, edgelist)

groups = detect_communities_directed_modularity(adj)
rev, edge_w = build_reverse_adj(adj)
nout, nin, m = directed_degrees(adj)
dmQ = directed_modularity(adj, [groups[i] for i in 1:tnodes]; nout=nout, nin=nin, m=m, edge_w=edge_w)
println("Directed modularity Q: ", round(dmQ, digits=4))

println("Loaded nodes=", tnodes, ", edges=", length(edgelist))

seeds = pick_seeds_metaquota(k, adj, groups; alpha_size=0.4, alpha_flow=0.6, R=180, L=7, prune_per_group=30)
println("Amount of seeds wanted: ", k)
println("Chosen seed: ", join(seeds, ","))
println("Seeds used (algorithm): ", length(seeds), "/", k)

println("\nDetected Groups:")
by_group = Dict{Int, Vector{Int}}()
for (node, group_id) in groups
    push!(get!(by_group, group_id, Int[]), node)
end
for (group_num, lbl) in enumerate(sort(collect(keys(by_group))))
    nodes = sort(by_group[lbl])
    formatted = join(["node $(n)" for n in nodes], ",")
    println("Group $(group_num): ", formatted)
end


trials = Int[]
for t in 1:100
    total_active = ic_trial_full(seeds, adj)                 
    influenced_only = total_active - length(seeds)          
    push!(trials, total_active)
    println("Trial $t: influenced=", influenced_only,
            " + seeds=", length(seeds),
            " => total=", influenced_only + length(seeds))
end
average_spread = sum(trials) / length(trials)
println("Average total (influenced + seeds): ", round(average_spread, digits=2))


rand_seeds = random_seeds(k, tnodes)
println("\nRandom baseline seeds: ", join(rand_seeds, ","))
println("Seeds used (baseline): ", length(rand_seeds), "/", k)

rand_trials = Int[]
for t in 1:10
    total_active = ic_trial_full(rand_seeds, adj)
    influenced_only = total_active - length(rand_seeds)
    push!(rand_trials, total_active)
    println("Baseline Trial $t: influenced=", influenced_only,
            " + seeds=", length(rand_seeds),
            " => total=", influenced_only + length(rand_seeds))
end
rand_average_spread = sum(rand_trials) / length(rand_trials)
println("Baseline average total (influenced + seeds): ", round(rand_average_spread, digits=2))


println("\nSide-by-side comparison per trial:")
for t in 1:min(length(trials), length(rand_trials))
    println("Round $t algorithm total: ", trials[t],
            " baseline total: ", rand_trials[t])
end
println("\nAlgorithm total avg: ", round(average_spread, digits=3),
        " | Baseline total avg: ", round(rand_average_spread, digits=3))